-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_theorem_2_1_saddle_props
-- name    : GabayMercier.DualAlgorithm.theorem_2_1_saddle_props
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:09:05.544096+00:00
-- url     : https://prove2.me/theorems/408e0a24-4f9e-4dd4-8f79-87e6414d2dfe
-- title:
--   Theorem 2.1 (first part) — a saddle point of ℒ gives the solution v*, y* = Av*, λ* ∈ ∂f(Av*), A'λ* = b
-- statement:
--   In the setting of (𝒫), let $f_2$ be proper and let $(v^*,y^*;\lambda^*)\in(V\times Y)\times Y$ be a saddle point of the Lagrangian
--   $$\mathcal L(v,y;\lambda)=f(y)+(\lambda,Av-y)-\langle b,v\rangle ,$$
--   that is, $\mathcal L(v^*,y^*;\lambda)\le\mathcal L(v^*,y^*;\lambda^*)\le\mathcal L(v,y;\lambda^*)$ for all $(v,y)$ and $\lambda$. Then (2.10) holds:
--   1. $v^*$ is a solution of (𝒫);
--   2. $y^*=Av^*$;
--   3. $\lambda^*\in\partial f(Av^*)$, where $f=f_1+f_2$;
--   4. $A'\lambda^*=b$, i.e. $(\lambda^*,Aw)=\langle b,w\rangle$ for every $w\in V$.
--
--   This direction identifies the primal part of any saddle point with the solution of (𝒫); the convergence proof of Section 3 is run against such a saddle point.
--
--   **Formalization Note.** $\partial f(Av^*)$ is the convex subdifferential of $f_1+f_2$ (as an `EReal`-valued function) with $Y'$ identified with $Y$, through `IsSubgradient`. The only hypothesis used is that $f_2$ is proper, which is part of the paper's standing assumption that $f_2$ maps into $(-\infty,+\infty]$ and is proper (p. 9); without it every triple is a saddle point.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 9, Theorem 2.1 (first sentence, (2.10) and footnote)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 2.1, p. 9, first part: any saddle point `(v*, y*; λ*)` of `ℒ` satisfies (2.10):
`v*` solves (𝒫), `y* = Av*`, `λ* ∈ ∂f(Av*)` and `A'λ* = b`. -/
theorem theorem_2_1_saddle_props (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (hf₂ : IsProperFn f₂) (vs : V) (ys ls : Y)
    (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    IsSolution A f₁ f₂ b vs ∧ ys = A vs ∧
      IsSubgradient (fun y => (f₁ y : EReal) + f₂ y) (A vs) ls ∧
      ∀ w : V, inner ℝ ls (A w) = b w := by sorry

end GabayMercier.DualAlgorithm
