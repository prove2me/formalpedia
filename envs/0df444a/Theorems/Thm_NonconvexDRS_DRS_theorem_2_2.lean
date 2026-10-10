-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_theorem_2_2
-- name    : NonconvexDRS.DRS.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:27.488461+00:00
-- url     : https://prove2.me/theorems/78e285a1-1379-4ddb-bbbb-8ca1e8bd90a7
-- title:
--   Theorem 2.2, p. 6 — lower bounds h(y) ≥ h(x) + ⟨∇h(x), y − x⟩ + ρ(y, x) for L-smooth σ-hypoconvex h, with L ≥ L_h, σ ∈ [−L, σ_h]
-- statement:
--   Let $h:\mathbb R^n\to\mathbb R$ be $L_h$-smooth and $\sigma_h$-hypoconvex, $\sigma_h\in[-L_h,L_h]$. Then for all $x,y\in\mathbb R^n$:
--
--   1. $h(y)\ge h(x)+\langle\nabla h(x),y-x\rangle+\frac{\sigma_h}2\|y-x\|^2$;
--   2. for every $L\ge L_h$ and every $\sigma$ with $-L<\sigma\le0$ and $\sigma\le\sigma_h$,
--   $$h(y)\ge h(x)+\langle\nabla h(x),y-x\rangle+\frac{\sigma L}{2(L+\sigma)}\|y-x\|^2+\frac1{2(L+\sigma)}\|\nabla h(y)-\nabla h(x)\|^2 .$$
--
--   At $L=L_h$, $\sigma=\sigma_h$ the second bound is Theorem 2.2(ii) as printed under the proviso $-L_h<\sigma_h\le0$; for general $(L,\sigma)$ it is the page's closing sentence ("all inequalities remain valid if one replaces $L_h$ with any $L\ge L_h$ and $\sigma_h$ with any $\sigma\in[-L,\sigma_h]$"), with the proviso of (ii) carried over. These lower bounds are the quantity $\rho(u,u^+)$ in the proof of the sufficient decrease Theorem 4.1.
--
--   **Formalization Note** The replacement clause is stated only for (ii), where it is needed (Case 1b of Theorem 4.1 uses $L=-2\sigma_{\varphi_1}/(2-\lambda)>L_{\varphi_1}$); for (i) it is an immediate weakening. The hypothesis $\sigma_h\in[-L_h,L_h]$ is the page's standing framing of §2.2.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 6, Theorem 2.2

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Theorem 2.2, p. 6, with (ii) in the extended form of its last sentence. -/
theorem theorem_2_2 {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (Lh σh : ℝ)
    (hsmooth : IsLSmooth h Lh) (hhypo : IsHypoconvex h σh) (hσ : -Lh ≤ σh ∧ σh ≤ Lh) :
    (∀ x y, h y ≥ h x + ⟪gradient h x, y - x⟫_ℝ + σh / 2 * ‖y - x‖ ^ 2) ∧
    ∀ L σ : ℝ, Lh ≤ L → -L < σ → σ ≤ 0 → σ ≤ σh → ∀ x y,
      h y ≥ h x + ⟪gradient h x, y - x⟫_ℝ + σ * L / (2 * (L + σ)) * ‖y - x‖ ^ 2 +
        1 / (2 * (L + σ)) * ‖gradient h y - gradient h x‖ ^ 2 := by sorry

end NonconvexDRS.DRS
