-- Prove2me | Theorems.Thm_GaussPart_lemma_3_13
-- name    : GaussPart.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:07.02145+00:00
-- url     : https://prove2.me/theorems/b518e57a-ba44-46cf-877b-59f5b729fe0e
-- title:
--   Lemma 3.13 — polynomial norms and Hermite moments under smoothness
-- statement:
--   Let $P=N(0,I_d)$, let $Q$ be $(q,\sigma)$-smooth with respect to $P$ ($q\ge1$, $\sigma\in(0,1]$), and $k\ge1$. For every polynomial $p$ of degree at most $k$
--   $$\mathbb E_Q[p^2]\le\frac{2q}{\sigma}(4q-1)^k\|p\|^2_{L^2(P)},$$
--   and for the normalized Hermite tensors $\mathcal H_i$, $i\in[k]$,
--   $$\big\|\mathbb E_Q[\mathcal H_i]\big\|_F\le e\Big(2q\log\frac{2eq}{\sigma}\Big)^{i/2}\le e\Big(2q\log\frac{2eq}{\sigma}\Big)^{k/2}.$$
--
--   These are the $V$- and $H$-bounds under which the moment discrepancy finder succeeds; a solver needs Gaussian hypercontractivity, which is not yet on the platform.
--
--   **Formalization Note** The first bound is `PolyMomentBound Q ((2q/σ)(4q−1)^k) k`, in lower integrals. $\mathbb E_Q[\mathcal H_i]$ is the entrywise Bochner integral; its entries are polynomials of degree $i\le k$, integrable under $Q$ by the first bound.
--
--   Differences from the source:
--   - encoding: E_Q[p²] ≤ (2q/σ)(4q − 1)^k ∥p∥²_{L²(P)} → PolyMomentBound Q ((2q/σ)(4q−1)^k) k (lower Lebesgue integrals; MvPolynomial of total degree ≤ k); reason: no integrability is presupposed
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.13, p.25 (PDF p.27); Hermite tensors, Appendix A, p.69

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.13** (Polynomial Norm under Smoothness).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.13, p.25 (PDF p.27); Hermite tensors,
Appendix A, p.69 (PDF p.71).

"Let P = N(0, I_d), let Q be (q, σ)-smooth with respect to P, where q ≥ 1 and σ ∈ (0, 1], and let
k ∈ ℕ₊. For every polynomial p of degree at most k, E_Q[p²] ≤ (2q/σ)(4q − 1)^k ∥p∥²_{L²(P)}.
Moreover, for the normalized Hermite tensors H_i, i ∈ [k], we have
∥E_Q[H_i]∥_F ≤ e(2q log(2eq/σ))^{i/2} ≤ e(2q log(2eq/σ))^{k/2}."

**Formalization Note.**
* The first assertion is `PolyMomentBound Q ((2q/σ)(4q − 1)^k) k`: polynomials are
  `MvPolynomial (Fin d) ℝ` of total degree at most `k`, and both sides are lower Lebesgue integrals
  of `p²`, so no integrability is presupposed.
* `E_Q[H_i]` is the entrywise Bochner integral `hermiteMoment Q i`; its entries are polynomials of
  degree `i ≤ k`, which the first assertion makes `Q`-integrable. `∥·∥_F` is `frobeniusNorm`. The
  exponents `i/2`, `k/2` are real (`Real.rpow`); `log` is natural. -/
theorem lemma_3_13 {d : ℕ} (Q : Measure (Vec d)) [IsProbabilityMeasure Q] (q σ : ℝ) (hq : 1 ≤ q)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hs : IsSmooth (stdGaussian (Vec d)) Q q σ) (k : ℕ) (hk : 1 ≤ k) :
    PolyMomentBound Q (2 * q / σ * (4 * q - 1) ^ k) k ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k →
        frobeniusNorm (hermiteMoment Q i) ≤
            Real.exp 1 * (2 * q * Real.log (2 * Real.exp 1 * q / σ)) ^ ((i : ℝ) / 2) ∧
          Real.exp 1 * (2 * q * Real.log (2 * Real.exp 1 * q / σ)) ^ ((i : ℝ) / 2) ≤
            Real.exp 1 * (2 * q * Real.log (2 * Real.exp 1 * q / σ)) ^ ((k : ℝ) / 2) := by sorry

end GaussPart
