-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_eq_top_of_notMem_support
-- name    : FunctorialResolution.Blowup.comap_eq_top_of_notMem_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:04.272966+00:00
-- url     : https://prove2.me/theorems/b3f65cb0-8cea-4c56-9db7-0a91c5bc598c
-- title:
--   Blowup: comap eq top of not Mem support
-- statement:
--   The Blowup construction uses the comap eq top of not Mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L30-L38

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.comap_eq_top_of_notMem_support {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) (h : ∀ x : X', f.base x ∉ I.support) :
    I.comap f = ⊤ := by sorry
