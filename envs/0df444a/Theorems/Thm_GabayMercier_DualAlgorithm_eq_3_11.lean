-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_11
-- name    : GabayMercier.DualAlgorithm.eq_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:10:05.153626+00:00
-- url     : https://prove2.me/theorems/1b5f3801-7435-41e5-b03d-eaae1d6efa4c
-- title:
--   (3.11) — r(A(vⁿ⁺¹ − v*), Av) = (r(yⁿ − y*) − (λⁿ − λ*), Av)
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), let $r>0$, $\rho>0$, let $(v^n,y^n,\lambda^n)_{n\ge0}$ be any run of the modified dual algorithm (3.4) and let $(v^*,y^*;\lambda^*)$ be a saddle point of $\mathcal L$. Then for every $n\ge0$,
--   $$r\bigl(A(v^{n+1}-v^*),Av\bigr)=\bigl(r(y^n-y^*)-(\lambda^n-\lambda^*),Av\bigr)\qquad\forall v\in V .$$
--
--   This is (3.5) minus (3.8): the error of Step 1 is driven only by the errors of the previous $y$- and $\lambda$-iterates.
--
--   **Formalization Note.** Step 1 and (3.8) are both used with the corrected sign $+\langle b,v\rangle$ (the paper prints $-$ in both); the $b$-terms cancel, so (3.11) is exactly as printed.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 16, (3.11)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (3.11), p. 16: subtracting (3.8) from (3.5). -/
theorem eq_3_11 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ n : ℕ, ∀ w : V, r * inner ℝ (A (v (n + 1) - vs)) (A w) =
      inner ℝ (r • (y n - ys) - (lam n - ls)) (A w) := by sorry

end GabayMercier.DualAlgorithm
