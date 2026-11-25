-- Prove2me | Theorems.Thm_GroundTheory_Global_algHom_kummerExtension_mem_fieldRange
-- name    : GroundTheory.Global.algHom_kummerExtension_mem_fieldRange
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:50:10.679868+00:00
-- url     : https://prove2.me/theorems/c4746e87-1f0c-4aea-aed4-c343b352550b
-- title:
--   Global: alg Hom kummer Extension mem field Range
-- statement:
--   The Global construction uses the alg Hom kummer Extension mem field Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L27-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L27-L69

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer
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
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]

theorem GroundTheory.Global.algHom_kummerExtension_mem_fieldRange (ι : kummerExtension K n Ω Δ →ₐ[K] E)
    (h : ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K)) (m : kummerExtension K n Ω Δ) :
    ι m ∈ (algebraMap F E).fieldRange := by sorry
