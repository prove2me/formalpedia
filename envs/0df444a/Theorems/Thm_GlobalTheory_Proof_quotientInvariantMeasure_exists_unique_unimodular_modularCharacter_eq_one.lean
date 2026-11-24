-- Prove2me | Theorems.Thm_GlobalTheory_Proof_quotientInvariantMeasure_exists_unique_unimodular_modularCharacter_eq_one
-- name    : GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.modularCharacter_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:23.427968+00:00
-- url     : https://prove2.me/theorems/93987929-fc38-4b6c-9228-0f59b3629090
-- title:
--   quotient Invariant Measure exists unique unimodular: modular Character eq one
-- statement:
--   The quotient Invariant Measure exists unique unimodular construction uses the modular Character eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientInvariantMeasureExistsUniqueUnimodular.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientInvariantMeasureExistsUniqueUnimodular.lean#L10-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientInvariantMeasureExistsUniqueUnimodular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular

theorem GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.modularCharacter_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (hG : IsUnimodular G) (g : G) :
    Measure.modularCharacter g = 1 := by sorry
