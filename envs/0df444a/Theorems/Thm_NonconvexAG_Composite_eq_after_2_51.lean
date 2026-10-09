-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_after_2_51
-- name    : NonconvexAG.Composite.eq_after_2_51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:36:46.782653+00:00
-- url     : https://prove2.me/theorems/a929d202-062a-4c09-b3fd-e3e2c90335b3
-- title:
--   §2.2, display after (2.51) — the summed inequality over k = 1, …, N
-- statement:
--   In the setting of (2.51), fix $N\ge1$ and suppose that for $k=1,\dots,N$
--   $$\alpha_k\lambda_k\le\beta_k\qquad\text{and}\qquad\frac{\alpha_1}{\lambda_1\Gamma_1}\ge\frac{\alpha_2}{\lambda_2\Gamma_2}\ge\dots\ge\frac{\alpha_N}{\lambda_N\Gamma_N}$$
--   (the first half of (2.9), and (2.10)). Then for every $x\in K$
--   $$\frac{\Phi(x^{ag}_N)-\Phi(x)}{\Gamma_N}+\sum_{k=1}^N\frac{1-L_\Psi\beta_k}{2\beta_k\Gamma_k}\|x^{ag}_k-x^{md}_k\|^2\le\frac{\|x_0-x\|^2}{2\lambda_1}+\frac{L_f}2\sum_{k=1}^N\frac{\alpha_k}{\Gamma_k}\Big[\|x^{md}_k-x\|^2+\alpha_k(1-\alpha_k)\|x^{ag}_{k-1}-x_{k-1}\|^2\Big].$$
--
--   It is (2.51) summed with Lemma 1, the distance terms telescoping by (2.10).
--
--   **Formalization Note** The display is unnumbered in the paper. (2.9) and (2.10) are imposed only for $k=1,\dots,N$, the indices that occur.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 12, §2.2, display after (2.51)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- §2.2, display after (2.51), p. 12: the summed inequality, for every `N ≥ 1` and every `x` in
the domain `K` of `𝒳`, when `αₖλₖ ≤ βₖ` (first half of (2.9)) and (2.10) hold for `k = 1, …, N`. -/
theorem eq_after_2_51 {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) :
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ x ∈ K,
      (Φ (xag N) - Φ x) / NonconvexAG.Smooth.Gamma α N +
          ∑ k ∈ Finset.Icc 1 N,
            (1 - (Lf + Lh) * β k) / (2 * β k * NonconvexAG.Smooth.Gamma α k) * ‖xag k - xmd k‖ ^ 2 ≤
        ‖x0 - x‖ ^ 2 / (2 * lam 1) +
          Lf / 2 * ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k *
            (‖xmd k - x‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) - xk (k - 1)‖ ^ 2) := by sorry
end NonconvexAG.Composite
