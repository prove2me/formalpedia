-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_map_mem_nonZeroDivisors_of_iso
-- name    : FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:32.896817+00:00
-- url     : https://prove2.me/theorems/5f801f5d-d70a-4e8c-beb0-5c7697b48999
-- title:
--   Blowup: map mem non Zero Divisors of iso
-- statement:
--   The Blowup construction uses the map mem non Zero Divisors of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L10-L28

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
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

theorem FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso {A B : CommRingCat.{u}} (e : A ≅ B) {x : A}
    (hx : x ∈ nonZeroDivisors A) : e.hom.hom x ∈ nonZeroDivisors B := by sorry
