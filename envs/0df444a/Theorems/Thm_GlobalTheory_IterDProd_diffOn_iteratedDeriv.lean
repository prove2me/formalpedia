-- Prove2me | Theorems.Thm_GlobalTheory_IterDProd_diffOn_iteratedDeriv
-- name    : GlobalTheory.IterDProd.diffOn_iteratedDeriv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:30.105669+00:00
-- url     : https://prove2.me/theorems/f18b28e9-f86f-44a6-91ba-bf9006f91207
-- title:
--   Iter DProd: diff On iterated Deriv
-- statement:
--   The Iter DProd construction uses the diff On iterated Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedPartialDerivProdOneVarAtZero.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedPartialDerivProdOneVarAtZero.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.IterDProd

theorem GlobalTheory.IterDProd.diffOn_iteratedDeriv {r : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball 0 r) := by sorry
