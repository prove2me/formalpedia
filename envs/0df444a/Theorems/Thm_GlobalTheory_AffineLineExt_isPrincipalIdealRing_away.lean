-- Prove2me | Theorems.Thm_GlobalTheory_AffineLineExt_isPrincipalIdealRing_away
-- name    : GlobalTheory.AffineLineExt.isPrincipalIdealRing_away
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:55:23.732835+00:00
-- url     : https://prove2.me/theorems/26a49f3d-65fb-4a0b-8842-10cad2e75aa8
-- title:
--   Affine Line Ext: is Principal Ideal Ring away
-- statement:
--   The Affine Line Ext construction uses the is Principal Ideal Ring away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAffineLineMorphismToProperAcrossPoint.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAffineLineMorphismToProperAcrossPoint.lean#L12-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAffineLineMorphismToProperAcrossPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AffineLineExt
open Polynomial

theorem GlobalTheory.AffineLineExt.isPrincipalIdealRing_away {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := by sorry
