-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoSum_contDiffOn_modPt
-- name    : GlobalTheory.WeightTwoSum.contDiffOn_modPt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:44.735999+00:00
-- url     : https://prove2.me/theorems/6d1c3117-28e3-443e-849d-44f14eda1e9c
-- title:
--   Weight Two Sum: cont Diff On mod Pt
-- statement:
--   The Weight Two Sum construction uses the cont Diff On mod Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L86-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.WeightTwoSum.contDiffOn_modPt {Φ : Type} [Fintype Φ] (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) :
    ContDiffOn ℂ ∞ (modPt φ e θ) (polydisc I) := by sorry
