-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_prop9_b_bounds
-- name    : OTDRO.StrongCvx.prop9_b_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:22.640855+00:00
-- url     : https://prove2.me/theorems/6c5ca8e6-2e57-468c-9370-1d3f691775cc
-- title:
--   Proposition 9(b), p. 37 — curvature-margin and maximizer bounds
-- statement:
--   Under Assumptions 1–4 and $0<\delta<\delta_0$, for $P_0$-almost every $x$ and nonzero $(\beta,\lambda)\in\mathbb W$, the maximizing set $\Gamma^*(\beta,\lambda;x)$ is a singleton $\{g\}$. Its curvature margin and size satisfy
--
--   $$\varphi_g(\beta,\lambda;x)\ge\varphi_{\min}\|\beta\|,\qquad |g|\le\frac{|\ell'(\beta^{\mathsf T}x)|}{\varphi_{\min}\|\beta\|};$$
--
--   if $(\beta,\lambda)\in\mathbb V$, also $|g|\ge|\ell'(\beta^{\mathsf T}x)|/(2K_2\|\beta\|)$. These are the bounds of (33) used for the Hessian estimates.
--
--   **Formalization Note** The printed strict sign in the first bound is corrected to $\ge$: equality is possible, and the proof on p. 56 derives a nonstrict inequality. The canonical selection is the unique maximizer on $\mathbb W$, represented by the infimum of its singleton maximizing set.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Proposition 9(b) and (33), p. 37; proof p. 56

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Kernel

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Proposition 9(b), p. 37, with its printed strict φ_g inequality
corrected to ≥, the relation proved on p. 56. On W the maximizer is unique,
so `selectedGamma` is the paper's measurable selection g there. -/
theorem prop9_b_bounds {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (hB4 : Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ) (hL : DerivSqBounds P0 ℓ B Llow Lbar)
    (hδ0 : δ < delta0 ρmin ρmax Llow (Rbeta B) M) :
    ∀ᵐ x ∂P0, ∀ θ ∈ regionW B δ M (Rbeta B) ρmin ρmax Llow Lbar,
      θ.1 ≠ 0 →
      let g := selectedGamma ℓ A δ θ.1 θ.2 x
      OTDRO.Dual.maximizers ℓ A δ θ.1 θ.2 x = {g} ∧
      phiMin δ Llow ρmax (Rbeta B) M ρmin * ‖θ.1‖ ≤
        kernelPhi ℓ A δ g θ.1 θ.2 x ∧
      (θ ∈ regionV B δ M (Rbeta B) ρmin ρmax Llow Lbar →
        |deriv ℓ (inner ℝ θ.1 x)| /
          (2 * K2 δ M (Rbeta B) ρmin Lbar * ‖θ.1‖) ≤ |g|) ∧
      |g| ≤ |deriv ℓ (inner ℝ θ.1 x)| /
        (phiMin δ Llow ρmax (Rbeta B) M ρmin * ‖θ.1‖) := by sorry

end OTDRO.StrongCvx
