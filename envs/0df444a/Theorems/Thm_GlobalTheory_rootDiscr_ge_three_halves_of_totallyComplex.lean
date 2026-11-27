-- Prove2me | Theorems.Thm_GlobalTheory_rootDiscr_ge_three_halves_of_totallyComplex
-- name    : GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:46.70681+00:00
-- url     : https://prove2.me/theorems/2c6d1e53-0833-4740-be2d-216fa93c6521
-- title:
--   Global Theory: root Discr ge three halves of totally Complex
-- statement:
--   The Global Theory construction uses the root Discr ge three halves of totally Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RootDiscrGeThreeHalvesOfIsTotallyComplex.lean#L10-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RootDiscrGeThreeHalvesOfIsTotallyComplex.lean#L10-L52

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RootDiscrGeThreeHalvesOfIsTotallyComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory
open MeasureTheory NumberField Finset

theorem GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K ∧
      (3 / 2 : ℝ) ≤ 2 * _root_.Formalism.HermitianLatticesTheory.vInv K ∧
      Real.sqrt |(discr K : ℝ)| = (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ _root_.Formalism.HermitianLatticesTheory.fDeg K := by sorry
