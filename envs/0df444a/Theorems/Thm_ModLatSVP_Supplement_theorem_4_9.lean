-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_4_9
-- name    : ModLatSVP.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:04.856614+00:00
-- url     : https://prove2.me/theorems/5cc39363-67f9-4727-a8a7-5a17d62acb84
-- title:
--   Theorem 4.9, p.31 — module rank in the input — SVP and CVP with $P^{n+4}2^{O(N)}n^{N/2}\rho^{(N-d)/2}$ and $P^{2n+8}2^{O(N)}(n!)^d\rho^{N/2}$ SVP-oracle calls, polynomial space
-- statement:
--   Let the module rank $n\ge1$ be part of the input, $N=nd$ and $P=N+6$. There are deterministic oracle algorithms and an absolute constant $C$ such that, for every rank-$n$ module $M\cong\mathbb Z^N$ over a totally real or CM field $K$ of degree $d$ with $\rho=\mathrm{rd}(K)$, in the input model of §2.2, and every exact SVP oracle:
--
--   1. exact SVP is solved with at most $\displaystyle\mathcal S_{n,d}=P^{n+4}\,2^{CN}\,n^{N/2}\,\rho^{(N-d)/2}$ oracle calls;
--   2. for every rational target $t$, a closest vector, and also the list of all closest vectors (each once), are computed with at most $\displaystyle\mathcal C_{n,d}=P^{2n+8}\,2^{CN}\,(n!)^{d}\,\rho^{N/2}$ oracle calls;
--
--   every call on a lattice of dimension at most $d+1$, with polynomial work per call (at most $(Q+1)(\ell+1)^k$ steps for the respective bound $Q$), and in polynomial working space $(\ell+1)^{k'}$ apart from the oracle, where the degrees $k,k'$ are absolute.
--
--   These uniform bounds are the input to the growing-rank analysis of §6 and, with Kannan's algorithm as the oracle, to Theorem 4.1.
--
--   **Formalization Note** Oracle model, call and step counts as in Theorem 4.5; working space of oracle runs is $\texttt{ModLatSVP.Supplement.OSpaceWithin}$ (the query stack counts, the oracle's own computation does not).
--
--   Differences from the source:
--   - reading: "the algorithms of Section 4 solve … using at most 𝒮_{n,d} and 𝒞_{n,d} exact SVP-oracle calls of dimension at most d + 1" → oracle machines that, for every valid exact SVP oracle, halt with the output within the call bound, with queries of dimension ≤ d + 1 and at most (Q + 1)(ℓ + 1)^k steps; reason: the oracle model of §4.1 with polynomial work per call (Lemma 4.8); without a step bound a call bound is empty
--   - reading: 2^{O(N)}, "the implied constants are absolute" → 2^{C·N} with C and the machines chosen before n and the instance; step and space degrees k, k' absolute; reason: Lemma 4.8: degree independent of the module rank
--   - encoding: exact CVP, including enumeration of all closest vectors → one machine outputting a closest vector, one outputting a duplicate-free list of exactly the closest vectors; reason: both tasks of the statement
--   - encoding: polynomial working space → OSpaceWithin (ℓ + 1)^{k'}: all stacks but the output stack, query stack included, output append-only; reason: the oracle's own computation is one step and uses no machine space
--   - encoding: module input, exact SVP oracle → as in ModLatSVP.Supplement.theorem_4_5; reason: same conventions
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 4.9, (23), (24), p.31 (PDF p.31); oracle model §4.1, p.24; Lemma 4.8, p.31

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

/-- **Theorem 4.9, §4.5, p.31: SVP and CVP with SVP-oracle calls, module rank part of the input.** Kim,
Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027
submission (manuscript sha256 e7151fad…): "Let the module rank n ≥ 1 be part of the input, and set N = nd
and P = N + 6. The algorithms of Section 4 solve exact SVP and CVP, including enumeration of all closest
vectors, using at most 𝒮_{n,d} and 𝒞_{n,d} exact SVP-oracle calls of dimension at most d + 1, where
𝒮_{n,d} ≤ P^{n+4} 2^{O(N)} n^{N/2} ρ^{(N−d)/2}, (23) 𝒞_{n,d} ≤ P^{2n+8} 2^{O(N)} (n!)^d ρ^{N/2}. (24) The
implied constants are absolute, and both reductions use polynomial working space."

There are oracle machines `OM_SVP`, `OM_CVP`, `OM_all` and absolute constants `C, k, k'` such that for every
`n ≥ 1`, every totally real or CM field `K` of degree `d` with `ρ = rd(K)`, every module input
`(d, c, S, G, A)` of a rank-`n` module `ℤ^N` (`N = n d`, `P = N + 6`) and every exact SVP oracle `O`:
1. `OM_SVP` outputs a shortest nonzero vector using at most `𝒮 = P^{n+4} 2^{C N} n^{N/2} ρ^{(N−d)/2}`
   oracle calls;
2. for every rational target `t`, `OM_CVP` outputs one closest vector and `OM_all` the list of all
   closest vectors (each once), each using at most `𝒞 = P^{2n+8} 2^{C N} (n!)^d ρ^{N/2}` oracle calls;
every call of dimension at most `d + 1`, at most `(Q + 1)(ℓ + 1)^k` steps for the respective call bound
`Q` (`ℓ` the input length), and working space at most `(ℓ + 1)^{k'}` apart from the oracle.

**Formalization Note.**
* Oracle model, call and step counting as in `ModLatSVP.Supplement.theorem_4_5`; working space is
  `OSpaceWithin` (all stacks but the output stack, query stack included, output append-only).
* "The implied constants are absolute": `C` and the machines are chosen before `n` and the instance; the
  degrees `k, k'` are absolute too (Lemma 4.8, p.31: "whose degree is independent of the module rank").
* "Solve exact CVP, including enumeration of all closest vectors" is stated as both tasks. -/
theorem theorem_4_9 :
    ∃ (OMs OMc OMa : HMBinPacking.OracleMachine) (C k k' : ℕ),
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ),
        (IsTotallyReal K ∨ IsCMField K) → IsStar K τ → RepresentsField K τ ω c S →
        RepresentsModule K τ ω G A → N = n * d →
        ∀ O : List Bool → List Bool, IsSVPOracle O →
          ((∃ x : Fin N → ℤ, IsShortest G x ∧
              OCallsWithin OMs O (encModule d N c S G A) (encIntVec x)
                (((N : ℝ) + 6) ^ (n + 4) * 2 ^ (C * N) * (n : ℝ) ^ ((N : ℝ) / 2) *
                  rd K ^ (((N : ℝ) - d) / 2)) (d + 1) k) ∧
            OSpaceWithin OMs O (encModule d N c S G A) (((encModule d N c S G A).length + 1) ^ k')) ∧
          ∀ t : Fin N → ℚ,
            ((∃ x : Fin N → ℤ, IsClosest G t x ∧
                OCallsWithin OMc O (encModule d N c S G A ++ SpikyCVP.encVec t) (encIntVec x)
                  (((N : ℝ) + 6) ^ (2 * n + 8) * 2 ^ (C * N) * ((n.factorial : ℕ) : ℝ) ^ d *
                    rd K ^ ((N : ℝ) / 2)) (d + 1) k) ∧
              OSpaceWithin OMc O (encModule d N c S G A ++ SpikyCVP.encVec t)
                (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) ∧
            ((∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
                OCallsWithin OMa O (encModule d N c S G A ++ SpikyCVP.encVec t)
                  (xs.flatMap encIntVec)
                  (((N : ℝ) + 6) ^ (2 * n + 8) * 2 ^ (C * N) * ((n.factorial : ℕ) : ℝ) ^ d *
                    rd K ^ ((N : ℝ) / 2)) (d + 1) k) ∧
              OSpaceWithin OMa O (encModule d N c S G A ++ SpikyCVP.encVec t)
                (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) := by sorry

end Supplement

end ModLatSVP
