-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_of_isFrechetSpace
-- name    : GarrettFA.isQuasiComplete_of_isFrechetSpace
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:32:42.76917+00:00
-- url     : https://prove2.me/theorems/3983194b-53a4-4d69-b344-90faae6de3e4
-- title:
--   §4 — Fréchet spaces are quasi-complete
-- statement:
--   Every Fréchet space $X$ over $\mathbb K=\mathbb R$ or $\mathbb C$ is quasi-complete:
--
--   $$X \text{ Fréchet}\ \Longrightarrow\ \text{every bounded Cauchy net in } X \text{ converges}.$$
--
--   In particular, Banach and Hilbert spaces are quasi-complete.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, remark after Definition 4.0.2 ("Complete metric spaces are quasi-complete, so Hilbert, Banach, and Fréchet spaces are quasi-complete")

import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsFrechetSpace

namespace GarrettFA
theorem isQuasiComplete_of_isFrechetSpace {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : IsFrechetSpace 𝕜 X) :
    IsQuasiComplete 𝕜 X := by sorry
end GarrettFA
