-- Prove2me | Theorems.Thm_GarrettFA_not_isNetComplete_weakDual_of_isFrechetSpace
-- name    : GarrettFA.not_isNetComplete_weakDual_of_isFrechetSpace
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:35:55.211075+00:00
-- url     : https://prove2.me/theorems/fd68c458-021f-4ce1-98b8-3e05906fa345
-- title:
--   Cor. 5.0.2 — weak duals of infinite-dimensional Fréchet spaces are not complete
-- statement:
--   Let $X$ be an infinite-dimensional Fréchet space over $\mathbb K=\mathbb R$ or $\mathbb C$, for instance an infinite-dimensional Banach or Hilbert space. Then its weak dual is not complete: some Cauchy net in $X^*_\sigma$ does not converge.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, Corollary 5.0.2 (Hilbert, Banach and Fréchet cases)

import Definitions.Def_GarrettFA_IsNetComplete
import Definitions.Def_GarrettFA_IsFrechetSpace

namespace GarrettFA
theorem not_isNetComplete_weakDual_of_isFrechetSpace {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : IsFrechetSpace 𝕜 X) (hinf : ¬ FiniteDimensional 𝕜 X) :
    ¬ IsNetComplete (WeakDual 𝕜 X) := by sorry
end GarrettFA
