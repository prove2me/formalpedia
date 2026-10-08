-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_12
-- name    : GabayMercier.DualAlgorithm.eq_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:09:52.420638+00:00
-- url     : https://prove2.me/theorems/fcd80935-2c67-4781-83ae-ebfe47f5fe4e
-- title:
--   (3.12) — A(vⁿ⁺¹ − v*) = P(yⁿ − y*) − (1/r) P(λⁿ − λ*)
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), let $r>0$, $\rho>0$, let $(v^n,y^n,\lambda^n)$ be a run of the modified dual algorithm (3.4) and $(v^*,y^*;\lambda^*)$ a saddle point of $\mathcal L$. Let $P$ be the orthogonal projection of $Y$ onto the range $R(A)$, which is closed by (2.5). Then for every $n\ge0$
--   $$A(v^{n+1}-v^*)=P(y^n-y^*)-\frac1r\,P(\lambda^n-\lambda^*) .$$
--
--   This explicit form of (3.11) expresses the $v$-error through projected $y$- and $\lambda$-errors; it is used both in the energy estimate (3.13)–(3.19) and to transfer convergence from $P(\lambda^n-\lambda^*)$ and $y^n$ to $v^n$.
--
--   **Formalization Note.** $P$ is `projRange A`, the orthogonal projection onto the closure of $R(A)$; under (2.5) this closure is $R(A)$ itself.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 16, (3.12)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (3.12), p. 16: `A(vⁿ⁺¹ − v*) = P(yⁿ − y*) − (1/r) P(λⁿ − λ*)`, with `P` the orthogonal
projection onto `R(A)`. -/
theorem eq_3_12 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ n : ℕ, A (v (n + 1) - vs) =
      projRange A (y n - ys) - (1 / r) • projRange A (lam n - ls) := by sorry

end GabayMercier.DualAlgorithm
