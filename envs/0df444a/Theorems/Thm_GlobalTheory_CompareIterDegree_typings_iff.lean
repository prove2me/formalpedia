-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_typings_iff
-- name    : GlobalTheory.CompareIterDegree.typings_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:30.810135+00:00
-- url     : https://prove2.me/theorems/341d9fad-9a58-5024-a512-32ada327a071
-- title:
--   Compare Iter Degree: typings iff
-- statement:
--   The Compare Iter Degree construction uses the typings iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L526-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L526-L537

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords

theorem GlobalTheory.CompareIterDegree.typings_iff :
    (FormalDegreeSubsetSum ∧ IteratedHighestWeightBound ∧ DegSetBound ∧ DegStepBound ∧ DegVand) ↔ Statement := by sorry
