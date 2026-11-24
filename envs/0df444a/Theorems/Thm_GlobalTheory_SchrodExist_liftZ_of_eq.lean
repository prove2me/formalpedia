-- Prove2me | Theorems.Thm_GlobalTheory_SchrodExist_liftZ_of_eq
-- name    : GlobalTheory.SchrodExist.liftZ_of_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:00.028308+00:00
-- url     : https://prove2.me/theorems/95357daa-ddbc-45d1-8018-081839362529
-- title:
--   Schrod Exist: lift Z of eq
-- statement:
--   The Schrod Exist construction uses the lift Z of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L151-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SchrodExist
open GlobalTheory.PlaceModel

theorem GlobalTheory.SchrodExist.liftZ_of_eq {A Z : Type} [AddCommGroup Z] [TopologicalSpace A] (Φ : SB A) {g : A × Z} (h : g.2 = 0) :
    liftZ Φ g = Φ.1 g.1 := by sorry
