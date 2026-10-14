-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_weakDual
-- name    : GarrettFA.isQuasiComplete_weakDual
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:36:51.749112+00:00
-- url     : https://prove2.me/theorems/41c0c175-0cfd-4491-8149-4c94cf3728c8
-- title:
--   Remark 5.0.3 — weak duals of Fréchet and LF-spaces are quasi-complete
-- statement:
--   Let $X$ be a Fréchet space or an LF-space over $\mathbb K=\mathbb R$ or $\mathbb C$. Then its weak dual $X^*_\sigma$ is quasi-complete: every bounded Cauchy net of continuous linear functionals converges in the weak-star topology.
--
--   The notes state that this suffices for applications such as integration of distribution-valued functions.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, Remark 5.0.3 (and the introduction, p. 1)

import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsFrechetSpace
import Definitions.Def_GarrettFA_IsLFSpace

namespace GarrettFA
theorem isQuasiComplete_weakDual {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : IsFrechetSpace 𝕜 X ∨ IsLFSpace 𝕜 X) :
    IsQuasiComplete 𝕜 (WeakDual 𝕜 X) := by sorry
end GarrettFA
