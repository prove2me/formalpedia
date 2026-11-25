-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_fac_nonneg
-- name    : GlobalTheory.CompareIterDegree.fac_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:16.182238+00:00
-- url     : https://prove2.me/theorems/210de0a9-5acb-4b95-8d4e-fed5ed1b2f15
-- title:
--   Compare Iter Degree: fac nonneg
-- statement:
--   The Compare Iter Degree construction uses the fac nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L214-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L214-L218

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

theorem GlobalTheory.CompareIterDegree.fac_nonneg {d t : ℝ} (hd : 1 ≤ |d|) (ht : |t| ≤ 1) : 0 ≤ (d + t) / d := by sorry
