-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_eq_comap_ker_of_isPullback_of_flat
-- name    : FunctorialResolution.EmbeddedResolution.ker_eq_comap_ker_of_isPullback_of_flat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:58.097803+00:00
-- url     : https://prove2.me/theorems/b82f3a84-c7be-485e-a901-934255a56bcb
-- title:
--   Embedded Resolution: ker eq comap ker of is Pullback of flat
-- statement:
--   The Embedded Resolution construction uses the ker eq comap ker of is Pullback of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelFlatBaseChange.lean#L343-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelFlatBaseChange.lean#L343-L375

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

theorem FunctorialResolution.EmbeddedResolution.ker_eq_comap_ker_of_isPullback_of_flat {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
    [QuasiCompact h] [QuasiCompact h'] [AlgebraicGeometry.Flat g] :
    h'.ker = h.ker.comap g := by sorry
