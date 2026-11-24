-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_pow_mul_mem
-- name    : GlobalTheory.ExtendLineBundle.exists_pow_mul_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:29.618601+00:00
-- url     : https://prove2.me/theorems/2487d083-e21a-43aa-a4d1-5a68889c0754
-- title:
--   Extend Line Bundle: exists pow mul mem
-- statement:
--   The Extend Line Bundle construction uses the exists pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L62-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]

theorem GlobalTheory.ExtendLineBundle.exists_pow_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U))
    (h : genericPoint X ∈ U) (ha : genericPoint X ∈ X.basicOpen a) {t : X.functionField}
    (ht : ∀ y ∈ X.basicOpen a, t ∈ localSubring y) :
    ∃ n : ℕ, ∀ x ∈ U, X.presheaf.germ U _ h a ^ n * t ∈ localSubring x := by sorry
