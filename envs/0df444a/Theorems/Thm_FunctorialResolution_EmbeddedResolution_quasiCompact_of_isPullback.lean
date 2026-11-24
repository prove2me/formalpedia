-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_quasiCompact_of_isPullback
-- name    : FunctorialResolution.EmbeddedResolution.quasiCompact_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:17.603237+00:00
-- url     : https://prove2.me/theorems/6b2b6a1f-32fe-4e85-8d79-70efac8f2403
-- title:
--   Embedded Resolution: quasi Compact of is Pullback
-- statement:
--   The Embedded Resolution construction uses the quasi Compact of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelFlatBaseChange.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelFlatBaseChange.lean#L71-L74

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.quasiCompact_of_isPullback {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h] :
    QuasiCompact h' := by sorry
