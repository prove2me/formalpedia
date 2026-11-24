-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_prod_alt
-- name    : GlobalTheory.CubeFace.prod_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:10.212131+00:00
-- url     : https://prove2.me/theorems/0b104051-4a45-4cb6-be09-43c64981d15f
-- title:
--   Cube Face: prod alt
-- statement:
--   The Cube Face construction uses the prod alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L69-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace

theorem GlobalTheory.CubeFace.prod_alt (f : Finset (Fin 3) → ℂ) :
    ∏ I : Finset (Fin 3), f I ^ ((-1 : ℤ) ^ (3 - I.card)) =
      (f ∅)⁻¹ * f {0} * f {1} * f {2} * (f {0, 1})⁻¹ * (f {0, 2})⁻¹ * (f {1, 2})⁻¹ *
        f {0, 1, 2} := by sorry
