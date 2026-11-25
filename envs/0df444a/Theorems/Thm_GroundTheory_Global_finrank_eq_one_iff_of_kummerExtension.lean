-- Prove2me | Theorems.Thm_GroundTheory_Global_finrank_eq_one_iff_of_kummerExtension
-- name    : GroundTheory.Global.finrank_eq_one_iff_of_kummerExtension
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:40.558469+00:00
-- url     : https://prove2.me/theorems/7b6dd770-ab78-4377-9c1c-cf5dbcefcca8
-- title:
--   Global: finrank eq one iff of kummer Extension
-- statement:
--   The Global construction uses the finrank eq one iff of kummer Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L89-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L89-L110

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

theorem GroundTheory.Global.finrank_eq_one_iff_of_kummerExtension [IsSepClosed Ω]
    (g : F ⊗[K] kummerExtension K n Ω Δ →ₐ[F] E) (hg : Function.Surjective g) :
    finrank F E = 1 ↔ ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K) := by sorry
