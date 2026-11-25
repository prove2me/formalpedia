-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_maximalUnramifiedExtensionFrobenius_iff
-- name    : GroundTheory.LocalField.eq_maximalUnramifiedExtensionFrobenius_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:11.869719+00:00
-- url     : https://prove2.me/theorems/128d02b2-9fe7-52f0-aa1b-8e783eab3f07
-- title:
--   Local Field: eq maximal Unramified Extension Frobenius iff
-- statement:
--   The Local Field construction uses the eq maximal Unramified Extension Frobenius iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramified.lean#L506-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramified.lean#L506-L511

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

theorem GroundTheory.LocalField.eq_maximalUnramifiedExtensionFrobenius_iff (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    ρ = maximalUnramifiedExtensionFrobenius K Ω ↔
      ∀ ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω), ρ ξ = ξ ^ Nat.card 𝓀[K] := by sorry
