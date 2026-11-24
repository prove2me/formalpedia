-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirt_contDiffOn
-- name    : GlobalTheory.HeckeTwo.GoodAdd.wirt_contDiffOn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:55.446032+00:00
-- url     : https://prove2.me/theorems/2c73fe65-d73e-428f-ad54-4df20dbda8ed
-- title:
--   Good Add: wirt cont Diff On
-- statement:
--   The Good Add construction uses the wirt cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAdd.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAdd.lean#L14-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.GoodAdd
variable {Φ : Type} [Fintype Φ]
open Classical

theorem GlobalTheory.HeckeTwo.GoodAdd.wirt_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (τ : Φ) (b : Bool) : ContDiffOn ℝ ∞ (wirt τ b f) U := by sorry
