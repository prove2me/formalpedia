-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_isUnit_of_away
-- name    : GlobalTheory.SecGlue.Red.isUnit_of_away
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:24.225983+00:00
-- url     : https://prove2.me/theorems/1491fc16-13ab-46d0-9d34-07a53db4e357
-- title:
--   Red: is Unit of away
-- statement:
--   The Red construction uses the is Unit of away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red

theorem GlobalTheory.SecGlue.Red.isUnit_of_away {R T : Type} [CommRing R] [CommRing T] [Algebra R T] (a : R)
    (ρ : Localization.Away a →+* T) (hρ : ρ.comp (algebraMap R _) = algebraMap R T) :
    IsUnit (algebraMap R T a) := by sorry
