-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_ker_comp_of_isOpenImmersion
-- name    : FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:49.013229+00:00
-- url     : https://prove2.me/theorems/076f52e6-b56b-4ec0-ab0a-32c9cf859211
-- title:
--   Blowup: comap ker comp of is Open Immersion
-- statement:
--   The Blowup construction uses the comap ker comp of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L457-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L457-L514

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion {A B C : Scheme.{u}} (j : A ⟶ B) (f : B ⟶ C)
    [IsOpenImmersion f] [QuasiCompact j] [QuasiCompact (j ≫ f)] :
    (j ≫ f).ker.comap f = j.ker := by sorry
