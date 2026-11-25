-- Prove2me | Theorems.Thm_GroundTheory_Global_finrank_eq_one_of_tensor_surjective
-- name    : GroundTheory.Global.finrank_eq_one_of_tensor_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:51:02.319595+00:00
-- url     : https://prove2.me/theorems/f5446e0c-7840-4b7f-ab32-f2f35670f1d9
-- title:
--   Global: finrank eq one of tensor surjective
-- statement:
--   The Global construction uses the finrank eq one of tensor surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L73-L87

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
omit [Algebra K E] [IsScalarTower K F E]

theorem GroundTheory.Global.finrank_eq_one_of_tensor_surjective {A : Type*} [CommRing A] [Algebra K A]
    (g : F ⊗[K] A →ₐ[F] E) (hg : Function.Surjective g)
    (hA : ∀ m : A, g (1 ⊗ₜ m) ∈ (algebraMap F E).fieldRange) : finrank F E = 1 := by sorry
