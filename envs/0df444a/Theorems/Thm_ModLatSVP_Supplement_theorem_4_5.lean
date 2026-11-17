-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_4_5
-- name    : ModLatSVP.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:22:01.366835+00:00
-- url     : https://prove2.me/theorems/7f625385-7794-4638-bc1d-a14bc04d7e66
-- title:
--   Theorem 4.5, p.29 — fixed rank $n$ — a reduced module flag and a shortest vector with $\mathrm{poly}_n(d)A_n^d\rho^{(n-1)d/2}$ SVP-oracle calls of dimension $\le d+1$
-- statement:
--   Fix a module rank $n\ge1$. There are constants $A_n,C>0$ and $k$ depending only on $n$, and a deterministic algorithm with access to an exact SVP oracle, such that the following holds. Let $M\cong\mathbb Z^N$, $N=nd$, be a rank-$n$ module over a totally real or CM field $K$ of degree $d$ with root discriminant $\rho=\mathrm{rd}(K)$, in the input model of §2.2. For every exact SVP oracle, the algorithm computes a reduced module flag of $M$ (as an adapted basis) and a shortest nonzero vector of $M$ using at most
--
--   $$Q=C\,(d+1)^{k}\,A_n^{\,d}\,\rho^{(n-1)d/2}$$
--
--   oracle calls, each on a lattice of dimension at most $d+1$, and polynomial work per call: at most $(Q+1)(\ell+1)^{k_2}$ steps in all, $\ell$ the input length.
--
--   The bound shows how the root discriminant enters the cost of preparing reduced flags: through $\rho^{(n-1)d/2}$.
--
--   **Formalization Note** The oracle machine and its counts are $\texttt{ModLatSVP.Supplement.OCallsWithin}$; the algorithm must succeed for every valid oracle, whichever shortest vector the oracle returns.
--
--   Differences from the source:
--   - reading: "Algorithm 1 computes … using at most Q exact SVP-oracle calls of dimension at most d + 1" → an oracle machine that, for every valid exact SVP oracle, halts with the output after at most Q calls, each a positive definite rational Gram matrix of dimension ≤ d + 1, and at most (Q + 1)(ℓ + 1)^{k_2} steps; reason: Algorithm 1 is one such machine; polynomial work per call is Lemma 3.2 (p.18) and Lemma 4.8 (p.31), and without a step bound a call bound is empty
--   - reading: poly_n(d) A_n^d → C (d + 1)^k A_n^d with C, k, A_n depending only on n; reason: every polynomial in d is at most C(d + 1)^k
--   - encoding: a reduced module flag → an adapted basis U of a reduced module flag (IsReducedFlagBasis), output as encIntMat U followed by the shortest vector; reason: Definition 2.2; every module flag has an adapted basis
--   - encoding: exact SVP oracle → IsSVPOracle: on the encoding of (m, G), m ≥ 1, G positive definite rational, returns some shortest nonzero vector; reason: the oracle of §4.1, p.24
--   - encoding: rank-n module over a totally real or CM field, ρ = rd(K) → module input with RepresentsField, RepresentsModule, IsStar, N = n·d; ρ = ModLatSVP.rd K; reason: the base mission's input model
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 4.5, p.29 (PDF p.29); oracle model §4.1, p.24; Definition 2.2, p.14

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_Supplement_IsSVPOracle
import Definitions.Def_ModLatSVP_Supplement_IsReducedFlagBasis

open NumberField

namespace ModLatSVP

namespace Supplement

/-- **Theorem 4.5, §4.3, p.29: a reduced module flag and a shortest vector with SVP-oracle calls, fixed
rank.** Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and
Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…): "For each fixed module rank n,
Algorithm 1 computes a reduced module flag and a shortest nonzero vector using at most
poly_n(d) A_n^d ρ^{(n−1)d/2} exact SVP-oracle calls of dimension at most d + 1, where A_n depends only
on n."

Fix `n ≥ 1`. There are an oracle machine `OM`, constants `A_n, C > 0` and degrees `k, k₂` (depending only
on `n`) such that for every totally real or CM field `K` of degree `d` with `ρ = rd(K)`, every module input
`(d, c, S, G, A)` of a rank-`n` module `ℤ^N`, `N = n d`, and every exact SVP oracle `O`, the machine with
oracle `O` outputs the encoding of an adapted basis `U` of a reduced module flag followed by a shortest
nonzero vector `x`, using at most `Q = C (d+1)^k A_n^d ρ^{(n−1)d/2}` oracle calls, each of dimension at most
`d + 1`, and at most `(Q + 1)(ℓ + 1)^{k₂}` steps (`ℓ` the input length).

**Formalization Note.**
* The oracle model is `ModLatSVP.Supplement.OCallsWithin` (on `HMBinPacking.OracleMachine`): the machine
  must succeed for every valid oracle, whichever shortest vector it returns. The step bound is the
  polynomial work per call of Lemma 3.2 and Lemma 4.8 (pp.18, 31); without it a call bound is empty.
* "Algorithm 1 computes" is read as: some deterministic oracle machine computes; the paper's
  algorithm is one such machine.
* `poly_n(d)` is `C (d+1)^k`. The reduced module flag is output as an adapted basis
  (`IsReducedFlagBasis`, Definition 2.2: reduced at every index `1 ≤ i ≤ n`). -/
theorem theorem_4_5 (n : ℕ) (hn : 1 ≤ n) :
    ∃ (OM : HMBinPacking.OracleMachine) (An C : ℝ) (k k₂ : ℕ), 0 < An ∧ 0 < C ∧
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ) (hN : N = n * d),
        (IsTotallyReal K ∨ IsCMField K) → IsStar K τ → RepresentsField K τ ω c S →
        RepresentsModule K τ ω G A →
        ∀ O : List Bool → List Bool, IsSVPOracle O →
          ∃ (U : Matrix (Fin N) (Fin N) ℤ) (x : Fin N → ℤ),
            IsReducedFlagBasis hN G A U ∧ IsShortest G x ∧
            OCallsWithin OM O (encModule d N c S G A) (encIntMat U ++ encIntVec x)
              (C * ((d : ℝ) + 1) ^ k * An ^ d * rd K ^ (((n : ℝ) - 1) * d / 2)) (d + 1) k₂ := by sorry

end Supplement

end ModLatSVP
