-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_corollary_18_2
-- name    : IncentiveAwarePricing.CORP.corollary_18_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:37.770776+00:00
-- url     : https://prove2.me/theorems/8657ce25-bc32-4b67-9db3-4175084de1b2
-- title:
--   Corollary 18.2, p. 88 — vector Freedman: P{∃k: ‖u_k‖ ≥ t, w_k ≤ σ²} ≤ (d + 1) exp(−(t²/2)/(σ² + Rt/3))
-- statement:
--   Let $(u_k)_{k\ge0}$ be a martingale with values in $\mathbb R^d$ with respect to a filtration $(\mathcal F_k)$ on a probability space, with $u_0=0$. Assume its differences $v_k=u_k-u_{k-1}$ satisfy $\|v_k\|\le R$ almost surely for $k\ge1$, and define the predictable quadratic variation
--   $$w_k=\sum_{j=1}^k\mathbb E\big[\|v_j\|^2\,\big|\,\mathcal F_{j-1}\big],\qquad w_0=0 .$$
--   Then for all $t\ge0$ and $\sigma^2>0$,
--   $$\mathbb P\big\{\exists k\ge0:\ \|u_k\|\ge t\ \text{and}\ w_k\le\sigma^2\big\}\le(d+1)\exp\Big(-\frac{t^2/2}{\sigma^2+Rt/3}\Big).$$
--
--   This is the vector case of Tropp's matrix Freedman inequality (Theorem 18.1); the paper uses it to concentrate the score of the likelihood (Lemma 5).
--
--   **Formalization Note** The paper conditions on $u_1,\dots,u_{j-1}$; the statement is given for an arbitrary filtration to which $u$ is adapted, which contains that case. The start $u_0=0$ is added (it is Tropp's $Y_0=0$; without it the constant martingale $u_k\equiv t$ is a counterexample).
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 88, Corollary 18.2, (130)–(131)

import Mathlib

open MeasureTheory

namespace IncentiveAwarePricing.CORP

/-- **Corollary 18.2** (vector Freedman inequality), p. 88, (130)–(131). Let `(u_k)_{k ≥ 0}` be a
martingale with values in `ℝ^d` with respect to a filtration `ℱ`, started at `u_0 = 0`, with
differences `v_k = u_k - u_{k-1}` satisfying `‖v_k‖ ≤ R` almost surely for `k ≥ 1`, and let
`w_k = ∑_{j=1}^k E[‖v_j‖² | ℱ_{j-1}]`. Then for all `t ≥ 0` and `σ² > 0`,
`P{∃ k ≥ 0 : ‖u_k‖ ≥ t and w_k ≤ σ²} ≤ (d + 1) exp(-(t²/2)/(σ² + R t/3))`. -/
theorem corollary_18_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (d : ℕ)
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hu : Martingale u ℱ μ) (hu0 : ∀ ω, u 0 ω = 0)
    (R : ℝ) (hR : 0 ≤ R) (hdiff : ∀ k, 1 ≤ k → ∀ᵐ ω ∂μ, ‖u k ω - u (k - 1) ω‖ ≤ R)
    (t σsq : ℝ) (ht : 0 ≤ t) (hσ : 0 < σsq) :
    let w : ℕ → Ω → ℝ := fun k =>
      ∑ j ∈ Finset.Icc 1 k, μ[fun ω => ‖u j ω - u (j - 1) ω‖ ^ 2 | ℱ (j - 1)]
    μ {ω | ∃ k, t ≤ ‖u k ω‖ ∧ w k ω ≤ σsq} ≤
      ENNReal.ofReal ((d + 1) * Real.exp (-(t ^ 2 / 2) / (σsq + R * t / 3))) := by sorry

end IncentiveAwarePricing.CORP
