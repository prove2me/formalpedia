-- Prove2me | Theorems.Thm_ModLatSVP_theorem_3_5
-- name    : ModLatSVP.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:06.833195+00:00
-- url     : https://prove2.me/theorems/b6683d08-1fdc-46b9-9d13-cf818b3f1943
-- title:
--   Theorem 3.5 — exact module-CVP listing all closest vectors in $2^{O(N)}\mathrm{poly}(B,N,\ell(t))$ time, chain supplied
-- statement:
--   Under the hypotheses of Theorem 3.4 (with constants depending only on $n_0,d_0,s_0,C_0$), there are a deterministic Turing machine and constants $C,k,k'$ such that for every rational target $t\in\mathbb Q^N$, on the input consisting of the module data, the chain data and $t$ ($\ell$ bits), the machine outputs the list of **all** closest vectors of $M$ to $t$, each exactly once, within
--
--   $$2^{C N}\,(\ell+1)^{k}\ \text{steps},$$
--
--   using working space at most $(\ell+1)^{k'}$; the output, which may consist of exponentially many vectors, is written to a write-only stream that does not count as working space.
--
--   This is the CVP half of the paper's first main result with a supplied chain.
--
--   Differences from the source:
--   - reading: deterministic algorithm, bit complexity, no machine model named → one deterministic Mathlib TM2 machine over Bool, run per input; halts within the budget with exactly the stated output (SpikyCVP.RunsWithin); reason: the bounds are up to polynomial factors in the input length, and 2^{O(N)}·poly(ℓ) time with poly(ℓ) space is closed under the polynomial overhead of simulating a word-RAM
--   - reading: polynomial working space; a write-only output stream is excluded from working space (§2.1, p.11) → SpaceWithin M inp ((ℓ+1)^{k'}): on every reachable configuration the stacks other than the output stack hold at most (ℓ+1)^{k'} symbols, and the output stack is append-only; reason: Mathlib has no space measure for TM2; counting the input stack costs nothing since the budget exceeds ℓ
--   - reading: poly(B, N, ℓ(t)) with B including the chain data → (ℓ+1)^k with ℓ the length of the encoded input (module data, chain data, target); C, k, k' chosen after n₀, d₀, s₀, C₀ and before the instance; reason: B, N and ℓ(t) are at most ℓ; 'the implied constants depend only on n₀, s₀, d₀, C₀'
--   - encoding: a module over 𝒪_{K₀} in the input model of §2.2 (field data and action matrices in the input) → ∀ number fields K : Type with involution τ and data (ω, c, S, G, A) satisfying RepresentsField and RepresentsModule; the machine reads only the encoded data; reason: the machine sees only the data, so ∀ K with representation predicates is the promise that the data represent some K; every number field is isomorphic to one in Type
--   - encoding: rd(K₀) ≤ C₀; nonzero module of rank at most n₀ → |∆_K| ≤ C₀^{[K:ℚ]}; 1 ≤ N ≤ n₀ [K:ℚ] (ModulePromise); reason: rd(K) = |∆_K|^{1/[K:ℚ]}; the module rank is N/[K:ℚ]
--   - encoding: a supplied chain of totally real or CM fields with integral bases, multiplication tables, inclusions, and involutions ⋆ compatible with the inclusions → a list of FieldLevel records (degree, table, involution matrix, inclusion matrix into K's integral basis) satisfying RepresentsChain; the chain fields being totally real or CM is not assumed; reason: inclusions into K determine the inclusions between levels by linear algebra; every subfield of a totally real or CM field is totally real or CM (ModLatSVP.subfield_star)
--   - reading: exact CVP … including enumeration of all closest vectors → the output is the concatenated encoding of a duplicate-free list xs with x ∈ xs ↔ IsClosest G t x; reason: the paper's enumeration outputs every point exactly once (Lemma 3.2, p.18); the stronger reading
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 3.5, §3.3, p.20 (PDF p.20)

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_TowerPromise
import Definitions.Def_ModLatSVP_RepresentsChain
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField

namespace ModLatSVP

/-- **Theorem 3.5, §3.3, p.20: exact module-CVP, all closest vectors, with a supplied subfield chain.**
Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*,
STOC 2027 submission (manuscript sha256 e7151fad…): "Under the hypotheses of Theorem 3.4, exact CVP on M
for any rational target t, including enumeration of all closest vectors, can be solved deterministically
in time 2^{O(N)} poly(B, N, ℓ(t)) and polynomial space. The implied constants depend only on
n₀, s₀, d₀, C₀."

There are a TM2 machine and constants `C, k, k'` (depending only on `n₀, d₀, s₀, C₀`) such that, under
the hypotheses of Theorem 3.4 and for every rational target `t ∈ ℚ^N`, on the input (module data, chain
data, target; `ℓ` bits) the machine outputs, within `2^{C·N} (ℓ+1)^k` steps and working space
`(ℓ+1)^{k'}`, the list of all closest vectors to `t`, each exactly once.

**Formalization Note.** Machine, budgets and working space as in `ModLatSVP.theorem_3_4`; `ℓ` includes
the target, so `poly(B, N, ℓ(t))` is `poly(ℓ)`. "Enumeration of all closest vectors" is read as: the
output is the concatenated encoding of a duplicate-free list `xs` whose members are exactly the closest
vectors (the proofs output each point "exactly once", Lemma 3.2, p.18). The output is written to an
append-only stack excluded from the space bound (§2.1, p.11: "A write-only output stream is excluded
from working space"). -/
theorem theorem_3_5 (n₀ d₀ s₀ : ℕ) (hn₀ : 1 ≤ n₀) (hd₀ : 1 ≤ d₀) (hs₀ : 2 ≤ s₀) (C₀ : ℚ)
    (hC₀ : 1 ≤ C₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k k' : ℕ),
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ)
        (Ls : List (FieldLevel d)) (t : Fin N → ℚ),
        IsStar K τ → RepresentsField K τ ω c S → RepresentsModule K τ ω G A →
        ModulePromise K n₀ C₀ N → RepresentsChain K τ ω s₀ d₀ Ls →
        (∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
          SpikyCVP.RunsWithin M (encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t)
            (xs.flatMap encIntVec)
            (2 ^ (C * N) * ((encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t).length + 1) ^ k)) ∧
        SpaceWithin M (encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t)
          (((encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t).length + 1) ^ k') := by sorry

end ModLatSVP
