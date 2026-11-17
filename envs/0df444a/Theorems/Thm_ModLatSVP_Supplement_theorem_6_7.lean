-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_6_7
-- name    : ModLatSVP.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:25:51.55094+00:00
-- url     : https://prove2.me/theorems/d3e41252-5d91-4f9b-8922-df2b896049f7
-- title:
--   Theorem 6.7, p.41 — CVP with a shared squared-distance bound — one or all closest vectors, including preparation, with $P^{3n+6}2^{O(N)}(n!)^{d/2}\rho^N$ SVP-oracle calls
-- statement:
--   Let the module rank $n\ge1$ be part of the input, $N=nd$ and $P=N+6$. There are deterministic oracle algorithms and an absolute constant $C$ such that, for every rank-$n$ module $M\cong\mathbb Z^N$ over a totally real or CM field $K$ of degree $d$ with $\rho=\mathrm{rd}(K)$, in the input model of §2.2, every rational target $t$ and every exact SVP oracle, a closest vector of $M$ to $t$, and the list of all closest vectors without repetition, are computed, including the preparation of a reduced module flag, with at most
--
--   $$P^{3n+6}\,2^{CN}\,(n!)^{d/2}\,\rho^{N}$$
--
--   oracle calls on lattices of dimension at most $d+1$, with polynomial work per call, and in polynomial working space apart from the oracle.
--
--   Compared with Theorem 4.9, the rank factor $(n!)^d$ improves to $(n!)^{d/2}$ at the cost of $\rho^N$ in place of $\rho^{N/2}$.
--
--   **Formalization Note** The machines take only the module and the target, so preparation is included. Oracle model and working space as in Theorem 4.9; the step and space degrees are absolute.
--
--   Differences from the source:
--   - reading: "Algorithm 3 finds a closest vector. A two-pass variant also streams all closest vectors … require at most … SVP-oracle calls" → oracle machines that, for every valid exact SVP oracle, output a closest vector, resp. a duplicate-free list of exactly the closest vectors, within the call bound, queries of dimension ≤ d + 1, at most (Q + 1)(ℓ + 1)^k steps; reason: Algorithm 3 and its two-pass variant are such machines; polynomial work per call is Lemma 4.8
--   - reading: the module rank (no lower bound stated in Theorem 6.7) → every n ≥ 1; reason: the statement has no rank restriction; at n = 1 preparation is trivial
--   - reading: 2^{O(N)}, "the implied constant is absolute"; polynomial working space apart from the oracle workspace → 2^{C·N} with C, machines and degrees k, k' chosen before n and the instance; OSpaceWithin (ℓ + 1)^{k'}; reason: absolute constant; Lemma 4.8 degree independent of the rank
--   - encoding: "Including preparation" → the machines' input is the module input followed by the target only; reason: the flag is prepared by the machine itself
--   - encoding: module input; exact SVP oracle → as in ModLatSVP.Supplement.theorem_4_5; reason: same conventions
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 6.7, (39), p.41 (PDF p.41); Algorithm 3, p.42; §6 convention N = nd, P = N + 6, p.37

import Mathlib
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_Supplement_IsSVPOracle

open NumberField

namespace ModLatSVP

namespace Supplement

/-- **Theorem 6.7, §6.3, p.41: CVP with a shared squared-distance bound.** Kim, Lee, Son, *Exact SVP and
CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "After reduced-flag preparation, Algorithm 3 finds a closest vector. A two-pass variant
also streams all closest vectors without repetition. Including preparation, both tasks require at most
P^{3n+6} 2^{O(N)} (n!)^{d/2} ρ^N (39) SVP-oracle calls of dimension at most d + 1, where the implied
constant is absolute. The algorithms use polynomial working space apart from the oracle workspace." (§6:
"Throughout this section, let N = nd and P = N + 6.")

There are oracle machines `OM_CVP`, `OM_all` and absolute constants `C, k, k'` such that for every `n ≥ 1`,
every totally real or CM field `K` of degree `d` with `ρ = rd(K)`, every module input `(d, c, S, G, A)` of a
rank-`n` module `ℤ^N` (`N = n d`, `P = N + 6`), every rational target `t` and every exact SVP oracle `O`,
`OM_CVP` outputs one closest vector and `OM_all` the list of all closest vectors, each exactly once, each
using at most `Q = P^{3n+6} 2^{C N} (n!)^{d/2} ρ^N` oracle calls of dimension at most `d + 1` and at most
`(Q + 1)(ℓ + 1)^k` steps, in working space `(ℓ + 1)^{k'}` apart from the oracle.

**Formalization Note.**
* "Including preparation": the machines take only the module and the target, and prepare the reduced
  flag themselves.
* The theorem states no lower bound on the rank, so every `n ≥ 1` is covered.
* Oracle model and working space as in `ModLatSVP.Supplement.theorem_4_9`; `C`, the machines and the
  degrees are chosen before `n` and the instance. -/
theorem theorem_6_7 :
    ∃ (OMc OMa : HMBinPacking.OracleMachine) (C k k' : ℕ),
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ) (t : Fin N → ℚ),
        (IsTotallyReal K ∨ IsCMField K) → IsStar K τ → RepresentsField K τ ω c S →
        RepresentsModule K τ ω G A → N = n * d →
        ∀ O : List Bool → List Bool, IsSVPOracle O →
          ((∃ x : Fin N → ℤ, IsClosest G t x ∧
              OCallsWithin OMc O (encModule d N c S G A ++ SpikyCVP.encVec t) (encIntVec x)
                (((N : ℝ) + 6) ^ (3 * n + 6) * 2 ^ (C * N) *
                  ((n.factorial : ℕ) : ℝ) ^ ((d : ℝ) / 2) * rd K ^ N) (d + 1) k) ∧
            OSpaceWithin OMc O (encModule d N c S G A ++ SpikyCVP.encVec t)
              (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) ∧
          ((∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
              OCallsWithin OMa O (encModule d N c S G A ++ SpikyCVP.encVec t) (xs.flatMap encIntVec)
                (((N : ℝ) + 6) ^ (3 * n + 6) * 2 ^ (C * N) *
                  ((n.factorial : ℕ) : ℝ) ^ ((d : ℝ) / 2) * rd K ^ N) (d + 1) k) ∧
            OSpaceWithin OMa O (encModule d N c S G A ++ SpikyCVP.encVec t)
              (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) := by sorry

end Supplement

end ModLatSVP
