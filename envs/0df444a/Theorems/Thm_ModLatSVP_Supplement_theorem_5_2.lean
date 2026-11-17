-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_5_2
-- name    : ModLatSVP.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:40.043637+00:00
-- url     : https://prove2.me/theorems/9358486f-b6c7-4ac7-9c3f-6bf7742b0ec0
-- title:
--   Theorem 5.2, p.34 — semistable lattices — one or all closest vectors with $32D\,42^D$ SVP-oracle calls; with Kannan, time $\mathrm{poly}\cdot D^{D/(2e)+o(D)}$
-- statement:
--   Let $L$ be a semistable lattice of dimension $D\ge1$, given by a positive definite rational Gram matrix $G$, and let $t$ be a rational target; the input is $D$, $G$ and $t$, of length $\ell$.
--
--   1. For every exact SVP oracle, deterministic oracle algorithms find a closest vector of $L$ to $t$, and list all closest vectors without repetition, each using at most
--
--   $$32D\cdot42^{D}$$
--
--   oracle calls on lattices of dimension at most $D+1$, with polynomial work per call, in polynomial working space apart from the oracle.
--
--   2. Without an oracle, deterministic algorithms find a closest vector and list all closest vectors without repetition in time
--
--   $$(\ell+1)^{k}\,D^{\,D/(2e)+g(D)}$$
--
--   and polynomial working space, for a fixed function $g$ with $g(D)/D\to0$ and an absolute $k$.
--
--   No module structure is needed; cyclotomic ideal lattices are one family of semistable lattices.
--
--   **Formalization Note** The input is $\texttt{SpikyCVP.encCVP}\ G\ t$. Oracle runs use $\texttt{OCallsWithin}$ and $\texttt{OSpaceWithin}$; the second clause uses plain TM2 machines with $\texttt{SpikyCVP.RunsWithin}$ and $\texttt{ModLatSVP.SpaceWithin}$.
--
--   Differences from the source:
--   - reading: "a deterministic reduction finds … using at most 32D 42^D exact SVP-oracle calls of dimension at most D + 1" → oracle machines that, for every valid exact SVP oracle, halt with the output within 32D·42^D calls of dimension ≤ D + 1 and (32D·42^D + 1)(ℓ + 1)^k steps; reason: the oracle model of §4.1 with polynomial work per call (Lemma 4.8); without a step bound a call bound is empty
--   - reading: "With Kannan's exact SVP algorithm, it runs in deterministic time poly(B, D, ℓ(t)) D^{D/(2e)+o(D)} and polynomial working space" → plain TM2 machines M_1, M_all with time ⌊(ℓ + 1)^k D^{D/(2e) + g(D)}⌋ and SpaceWithin (ℓ + 1)^{k'}, g : ℕ → ℝ with g(D)/D → 0 chosen before the instance; reason: Kannan's algorithm is the proof's instantiation of the oracle, not a hypothesis; poly(B, D, ℓ(t)) is (ℓ + 1)^k since B, D, ℓ(t) ≤ ℓ
--   - encoding: finds a closest vector, or streams all closest vectors without repetition → one machine outputting a closest vector, one outputting a duplicate-free list of exactly the closest vectors, in each clause; reason: both tasks of the statement
--   - encoding: semistable lattice of dimension D given by a positive definite rational Gram matrix → IsSemistable of G (over all integer D × k matrices of rank k), G positive definite, 1 ≤ D; input encCVP G t; reason: the definition of §5.1; dimension 0 is not a lattice in the paper's sense
--   - encoding: polynomial working space apart from the oracle workspace → OSpaceWithin (ℓ + 1)^{k'}; reason: the oracle's own computation is one step and uses no machine space
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 5.2, p.34 (PDF p.34); semistability §5.1, p.33; oracle model §4.1, p.24

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin
import Definitions.Def_ModLatSVP_Supplement_IsSVPOracle
import Definitions.Def_ModLatSVP_Supplement_IsSemistable

open Filter Topology

namespace ModLatSVP

namespace Supplement

/-- **Theorem 5.2, §5.2, p.34: CVP for semistable lattices.** Kim, Lee, Son, *Exact SVP and CVP in
Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…): "Let L be a semistable lattice of dimension D given by a positive definite rational Gram
matrix, and let t be a rational target. A deterministic reduction finds a closest vector to t, or streams
all closest vectors without repetition, using at most 32D 42^D exact SVP-oracle calls of dimension at most
D + 1. The reduction uses polynomial working space apart from the oracle workspace. With Kannan's exact SVP
algorithm, it runs in deterministic time poly(B, D, ℓ(t)) D^{D/(2e)+o(D)} and polynomial working space."

There are oracle machines `OM₁`, `OM_all`, TM2 machines `M₁`, `M_all`, a function `g` with `g(D)/D → 0`
and absolute degrees `k, k'` such that for every `D ≥ 1`, every positive definite rational `D × D` Gram
matrix `G` of a semistable lattice and every rational target `t` (input `D, G, t`, `ℓ` bits):
1. for every exact SVP oracle `O`, `OM₁` outputs one closest vector and `OM_all` the list of all closest
   vectors, each exactly once, each using at most `32 D 42^D` oracle calls of dimension at most `D + 1`
   and at most `(32 D 42^D + 1)(ℓ + 1)^k` steps, in working space `(ℓ + 1)^{k'}` apart from the oracle;
2. `M₁` outputs one closest vector and `M_all` the list of all closest vectors, each exactly once, within
   `(ℓ + 1)^k D^{D/(2e) + g(D)}` steps and working space `(ℓ + 1)^{k'}`.

**Formalization Note.**
* No module structure: the input is `SpikyCVP.encCVP G t` (`D`, the Gram matrix, the target).
* Oracle model as in `ModLatSVP.Supplement.theorem_4_5`, working space of oracle runs `OSpaceWithin`;
  the second clause is a plain machine (the oracle replaced by an algorithm), with time
  `SpikyCVP.RunsWithin` and space `ModLatSVP.SpaceWithin`. Kannan's algorithm is how the paper proves
  the second clause; it is not a hypothesis.
* `+o(D)` is one function `g` with `g(D)/D → 0`, chosen before the instance; `poly(B, D, ℓ(t))` is
  `(ℓ + 1)^k`.
* `D ≥ 1`: a lattice of dimension `0` is excluded (there `D^{…}` could be `0`). -/
theorem theorem_5_2 :
    ∃ (OM₁ OMa : HMBinPacking.OracleMachine) (M₁ Ma : Turing.TM2ComputableAux Bool Bool)
      (g : ℕ → ℝ) (k k' : ℕ), Tendsto (fun m : ℕ => g m / m) atTop (𝓝 0) ∧
      ∀ (D : ℕ) (G : Matrix (Fin D) (Fin D) ℚ) (t : Fin D → ℚ), 1 ≤ D →
        (G.map (fun q : ℚ => (q : ℝ))).PosDef → IsSemistable (G.map (fun q : ℚ => (q : ℝ))) →
        (∀ O : List Bool → List Bool, IsSVPOracle O →
          ((∃ x : Fin D → ℤ, IsClosest G t x ∧
              OCallsWithin OM₁ O (SpikyCVP.encCVP G t) (encIntVec x)
                (32 * (D : ℝ) * 42 ^ D) (D + 1) k) ∧
            OSpaceWithin OM₁ O (SpikyCVP.encCVP G t) (((SpikyCVP.encCVP G t).length + 1) ^ k')) ∧
          ((∃ xs : List (Fin D → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
              OCallsWithin OMa O (SpikyCVP.encCVP G t) (xs.flatMap encIntVec)
                (32 * (D : ℝ) * 42 ^ D) (D + 1) k) ∧
            OSpaceWithin OMa O (SpikyCVP.encCVP G t) (((SpikyCVP.encCVP G t).length + 1) ^ k'))) ∧
        ((∃ x : Fin D → ℤ, IsClosest G t x ∧
            SpikyCVP.RunsWithin M₁ (SpikyCVP.encCVP G t) (encIntVec x)
              ⌊(((SpikyCVP.encCVP G t).length : ℝ) + 1) ^ k *
                (D : ℝ) ^ ((D : ℝ) / (2 * Real.exp 1) + g D)⌋₊) ∧
          SpaceWithin M₁ (SpikyCVP.encCVP G t) (((SpikyCVP.encCVP G t).length + 1) ^ k')) ∧
        ((∃ xs : List (Fin D → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
            SpikyCVP.RunsWithin Ma (SpikyCVP.encCVP G t) (xs.flatMap encIntVec)
              ⌊(((SpikyCVP.encCVP G t).length : ℝ) + 1) ^ k *
                (D : ℝ) ^ ((D : ℝ) / (2 * Real.exp 1) + g D)⌋₊) ∧
          SpaceWithin Ma (SpikyCVP.encCVP G t) (((SpikyCVP.encCVP G t).length + 1) ^ k')) := by sorry

end Supplement

end ModLatSVP
