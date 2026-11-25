-- Prove2me | Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one
-- name    : GroundTheory.LocalField.maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:09.411821+00:00
-- url     : https://prove2.me/theorems/c470dd64-7859-5975-9a68-1bacd5b5f519
-- title:
--   Local Field: maximal Unramified Extension Frobenius apply of pow eq one
-- statement:
--   The Local Field construction uses the maximal Unramified Extension Frobenius apply of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramified.lean#L518-L521
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramified.lean#L518-L521

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
variable [HasUnramifiedRoots K Ω]
variable [IsGalois K Ω]

theorem GroundTheory.LocalField.maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one {ξ : maximalUnramifiedExtension K Ω} {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) (hξ : ξ ^ m = 1) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] := by sorry
