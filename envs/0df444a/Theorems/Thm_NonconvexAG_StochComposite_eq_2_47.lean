-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_2_47
-- name    : NonconvexAG.StochComposite.eq_2_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:59.501529+00:00
-- url     : https://prove2.me/theorems/c70f2d43-ad54-4042-b153-463ac2cc07b3
-- title:
--   (2.47) — the L_f-corrected convexity gap at x^md_k, along Algorithm 4
-- statement:
--   Let $\Psi=f+h$ be as in Lemma 5 and run Algorithm 4 along any realization of the oracle samples. Then for every $k\ge1$ and every $x\in\mathbb R^n$,
--   $$\Psi(x^{md}_k)-\big[(1-\alpha_k)\Psi(x^{ag}_{k-1})+\alpha_k\Psi(x)\big]\le\langle\nabla\Psi(x^{md}_k),x^{md}_k-\alpha_kx-(1-\alpha_k)x^{ag}_{k-1}\rangle+\frac{L_f\alpha_k}2\|x^{md}_k-x\|^2+\frac{L_f\alpha_k^2(1-\alpha_k)}2\|x^{ag}_{k-1}-x_{k-1}\|^2 .$$
--
--   This is where the possible nonconvexity of $f$ enters the analysis, through the constant $L_f$ only.
--
--   **Formalization Note** Pathwise. $\Psi$, $\nabla\Psi$ and $L_\Psi$ are given with the identities $\Psi=f+h$, $\nabla\Psi=\nabla f+\nabla h$, $L_\Psi=L_f+L_h$. Restated from mission 2 of this series (there along Algorithm 2) because drafts cannot import one another; only (2.2) is used, so it holds along Algorithm 4 as well.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 12, (2.47)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (2.47), p. 12 (outer ends of the chain), along Algorithm 4 on `Ψ = f + h`, for every
realization `ω`, every `k ≥ 1` and every `x ∈ ℝⁿ`. -/
theorem eq_2_47 {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (P : E n → E n → ℝ → E n) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ x : E n,
      Ψ (xmd k ω) - ((1 - α k) * Ψ (xag (k - 1) ω) + α k * Ψ x) ≤
        inner ℝ (gΨ (xmd k ω)) (xmd k ω - α k • x - (1 - α k) • xag (k - 1) ω) +
          Lf * α k / 2 * ‖xmd k ω - x‖ ^ 2 +
          Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 := by sorry

end NonconvexAG.StochComposite
