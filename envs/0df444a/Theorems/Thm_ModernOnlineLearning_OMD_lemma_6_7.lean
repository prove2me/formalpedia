-- Prove2me | Theorems.Thm_ModernOnlineLearning_OMD_lemma_6_7
-- name    : ModernOnlineLearning.OMD.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:55.434248+00:00
-- url     : https://prove2.me/theorems/321e8346-5d4a-4447-ae61-6382fb7e02bc
-- title:
--   Lemma 6.7, p. 64 — Bregman three-point identity
-- statement:
--   Let $\psi$ be strictly convex on its domain $X$ and differentiable on $\operatorname{int}X$. For $x,y\in\operatorname{int}X$ and $z\in X$, its Bregman divergence obeys
--
--   $$B_\psi(z;x)+B_\psi(x;y)-B_\psi(z;y)=\langle\nabla\psi(y)-\nabla\psi(x),z-x\rangle.$$
--
--   The identity reorganizes three divergence terms into one dual pairing; it is used in the one-step analysis of mirror descent.
--
--   **Formalization Note** Gradients are Fréchet derivatives in the continuous dual. The statement assumes differentiability on the interior, as Definition 6.4 does; the related published Beck–Teboulle identity assumes the stronger $C^1$ condition and therefore is not used as an exact reference.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 6.7, p. 64

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.OMD

/-- Orabona, Lemma 6.7, p. 64, with only the differentiability required by
Definition 6.4. -/
theorem lemma_6_7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : Set E) (ψ : E → ℝ)
    (hstrict : StrictConvexOn ℝ X ψ)
    (hdiff : DifferentiableOn ℝ ψ (interior X))
    (x y z : E) (hx : x ∈ interior X) (hy : y ∈ interior X) (hz : z ∈ X) :
    BeckTeboulleMD.EMDA.bregman ψ z x +
      BeckTeboulleMD.EMDA.bregman ψ x y -
      BeckTeboulleMD.EMDA.bregman ψ z y =
        (fderiv ℝ ψ y - fderiv ℝ ψ x) (z - x) := by sorry

end ModernOnlineLearning.OMD
