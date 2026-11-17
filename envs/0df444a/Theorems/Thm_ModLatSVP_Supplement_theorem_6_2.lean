-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_6_2
-- name    : ModLatSVP.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:24:45.620443+00:00
-- url     : https://prove2.me/theorems/44d9f3a1-57d6-44f8-ac16-2187d2ef5561
-- title:
--   Theorem 6.2, pp.38–39 — squared-radius allocation, rank $n\ge2$ — $(N+6)^{n+2}2^{O(N)}n^{N/(2e)}\rho^{N/\sqrt e}$ and $(N+6)^{n+2}2^{O(N)}\rho^{d/2}e^{d\Psi_{n-1}(\rho)}$ SVP-oracle calls
-- statement:
--   Let the module rank $n\ge2$ be part of the input and $N=nd$. Algorithm 1, with every search performed by squared-radius allocation (Lemma 6.1), remains exact: for every rank-$n$ module $M\cong\mathbb Z^N$ over a totally real or CM field $K$ of degree $d$ with $\rho=\mathrm{rd}(K)$, in the input model of §2.2, and every exact SVP oracle, it computes a reduced module flag (as an adapted basis) and a shortest nonzero vector using at most
--
--   $$(N+6)^{n+2}\,2^{CN}\,n^{N/(2e)}\,\rho^{N/\sqrt e}\qquad\text{and at most}\qquad (N+6)^{n+2}\,2^{CN}\,\rho^{d/2}\exp\big(d\,\Psi_{n-1}(\rho)\big)$$
--
--   oracle calls on lattices of dimension at most $d+1$, with polynomial work per call, where $C$ is an absolute constant and $\Psi_m$ is defined in (31).
--
--   Compared with Theorem 4.9, the rank factor $n^{N/2}$ improves to $n^{N/(2e)}$.
--
--   **Formalization Note** One oracle machine meets both bounds: its call count is at most their minimum, and its step count at most $(\min+1)(\ell+1)^k$ with an absolute $k$. Oracle model as in Theorem 4.5.
--
--   Differences from the source:
--   - reading: "Run Algorithm 1 with every search performed by Lemma 6.1. The algorithm remains exact … it uses at most …" → an oracle machine that, for every valid exact SVP oracle, outputs an adapted basis of a reduced module flag and a shortest nonzero vector, with calls ≤ min(Q_1, Q_2) of dimension ≤ d + 1 and at most (min(Q_1, Q_2) + 1)(ℓ + 1)^k steps; reason: the modified Algorithm 1 is one such machine and its output is that of Algorithm 1 (Theorem 4.5); polynomial work per call is Lemma 4.8, which covers §6
--   - reading: 2^{O(N)}, "the implied constants are absolute" → 2^{C·N} with C, the machine and the step degree k chosen before n and the instance; reason: absolute constants; Lemma 4.8 degree independent of the rank
--   - encoding: reduced module flag; exact SVP oracle; module input → IsReducedFlagBasis, IsSVPOracle, module input as in ModLatSVP.Supplement.theorem_4_5; reason: same conventions
--   - encoding: Ψ_{n−1}(ρ) of (31); n^{N/(2e)}, ρ^{N/√e} → Psi (n − 1) (rd K), the closed form of (31); real powers; reason: the paper's definition
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 6.2, (32), pp.38–39 (PDF pp.38–39); (31), p.38; §6 convention N = nd, P = N + 6, p.37

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_Supplement_IsSVPOracle
import Definitions.Def_ModLatSVP_Supplement_IsReducedFlagBasis
import Definitions.Def_ModLatSVP_Supplement_Lm

open NumberField

namespace ModLatSVP

namespace Supplement

/-- **Theorem 6.2, §6.2, pp.38–39: Algorithm 1 with squared-radius allocation.** Kim, Lee, Son, *Exact SVP
and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission
(manuscript sha256 e7151fad…): "Run Algorithm 1 with every search performed by Lemma 6.1. The algorithm
remains exact. For module rank n ≥ 2 given as part of the input, it uses at most
(N + 6)^{n+2} 2^{O(N)} n^{N/(2e)} ρ^{N/√e} (32) exact SVP-oracle calls of dimension at most d + 1. A refined
bound is (N + 6)^{n+2} 2^{O(N)} ρ^{d/2} exp(dΨ_{n−1}(ρ)). The implied constants are absolute." (§6:
"Throughout this section, let N = nd and P = N + 6.")

There are an oracle machine `OM` and absolute constants `C, k` such that for every `n ≥ 2`, every totally
real or CM field `K` of degree `d` with `ρ = rd(K)`, every module input `(d, c, S, G, A)` of a rank-`n`
module `ℤ^N` (`N = n d`) and every exact SVP oracle `O`, the machine with oracle `O` outputs (as Algorithm 1
does) an adapted basis `U` of a reduced module flag followed by a shortest nonzero vector `x`, using at most
`Q = min(Q₁, Q₂)` oracle calls, each of dimension at most `d + 1`, and at most `(Q + 1)(ℓ + 1)^k` steps,
where
`Q₁ = (N + 6)^{n+2} 2^{C N} n^{N/(2e)} ρ^{N/√e}` and `Q₂ = (N + 6)^{n+2} 2^{C N} ρ^{d/2} exp(d Ψ_{n−1}(ρ))`.

**Formalization Note.**
* Oracle model as in `ModLatSVP.Supplement.theorem_4_5`; one machine meets both bounds (the call count
  is at most each of them). `Ψ_m` is the closed form (31) (`ModLatSVP.Supplement.Psi`).
* "Run Algorithm 1 …; the algorithm remains exact" is read as: some deterministic oracle machine computes
  what Algorithm 1 computes (a reduced module flag and a shortest vector) within the bounds.
* "The implied constants are absolute": `C`, the machine and the step-bound degree `k` are chosen before
  `n` and the instance (Lemma 4.8, p.31, covers §6: degree independent of the rank). -/
theorem theorem_6_2 :
    ∃ (OM : HMBinPacking.OracleMachine) (C k : ℕ),
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ) (hN : N = n * d),
        (IsTotallyReal K ∨ IsCMField K) → IsStar K τ → RepresentsField K τ ω c S →
        RepresentsModule K τ ω G A →
        ∀ O : List Bool → List Bool, IsSVPOracle O →
          ∃ (U : Matrix (Fin N) (Fin N) ℤ) (x : Fin N → ℤ),
            IsReducedFlagBasis hN G A U ∧ IsShortest G x ∧
            OCallsWithin OM O (encModule d N c S G A) (encIntMat U ++ encIntVec x)
              (min
                (((N : ℝ) + 6) ^ (n + 2) * 2 ^ (C * N) * (n : ℝ) ^ ((N : ℝ) / (2 * Real.exp 1)) *
                  rd K ^ ((N : ℝ) / Real.sqrt (Real.exp 1)))
                (((N : ℝ) + 6) ^ (n + 2) * 2 ^ (C * N) * rd K ^ ((d : ℝ) / 2) *
                  Real.exp (d * Psi (n - 1) (rd K))))
              (d + 1) k := by sorry

end Supplement

end ModLatSVP
