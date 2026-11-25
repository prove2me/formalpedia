-- Prove2me | Theorems.Thm_GlobalTheory_HasLogGrowthEntries_of_continuousOn
-- name    : GlobalTheory.HasLogGrowthEntries.of_continuousOn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:29.426796+00:00
-- url     : https://prove2.me/theorems/258395a0-6c4c-42e3-a21f-7ecdc2496f84
-- title:
--   Has Log Growth Entries: of continuous On
-- statement:
--   The Has Log Growth Entries construction uses the of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L385-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L385-L387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ X l m n : Type*} [TopologicalSpace X]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.HasLogGrowthEntries

theorem GlobalTheory.HasLogGrowthEntries.of_continuousOn {A : X → Matrix m n ℂ} (hA : ContinuousOn A U) :
    HasLogGrowthEntries S w U A := by sorry
