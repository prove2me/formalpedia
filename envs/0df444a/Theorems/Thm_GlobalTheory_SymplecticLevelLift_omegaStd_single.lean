-- Prove2me | Theorems.Thm_GlobalTheory_SymplecticLevelLift_omegaStd_single
-- name    : GlobalTheory.SymplecticLevelLift.omegaStd_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:27.57261+00:00
-- url     : https://prove2.me/theorems/33b6137a-5d91-4e1f-9fc7-34f48f287879
-- title:
--   Symplectic Level Lift: omega Std single
-- statement:
--   The Symplectic Level Lift construction uses the omega Std single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSymplecticBasisCongrLevelMod.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSymplecticBasisCongrLevelMod.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSymplecticBasisCongrLevelMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymplecticLevelLift
open Matrix Module

theorem GlobalTheory.SymplecticLevelLift.omegaStd_single {h : ℕ} (i j : Fin h ⊕ Fin h) :
    omegaStd (Pi.single i 1) (Pi.single j 1) = (-Matrix.J (Fin h) ℤ) i j := by sorry
