-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirtWord_contDiffOn
-- name    : GlobalTheory.HeckeTwo.GoodAdd.wirtWord_contDiffOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:39.204352+00:00
-- url     : https://prove2.me/theorems/c7177cea-a4e8-4060-a05a-8b33904db065
-- title:
--   Good Add: wirt Word cont Diff On
-- statement:
--   The Good Add construction uses the wirt Word cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAdd.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAdd.lean#L25-L29

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

theorem GlobalTheory.HeckeTwo.GoodAdd.wirtWord_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (wirtWord w f) U := by sorry
