-- Prove2me | Theorems.Thm_GroundTheory_Global_kummerExtension_pow_eq
-- name    : GroundTheory.Global.kummerExtension_pow_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:17:39.142511+00:00
-- url     : https://prove2.me/theorems/9e5e6f14-d62c-4f2c-b3e8-8be218f24286
-- title:
--   Global: kummer Extension pow eq
-- statement:
--   The Global construction uses the kummer Extension pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L22-L25

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
omit [NeZero n] [HasEnoughRootsOfUnity K n] [IsScalarTower K F E]

theorem GroundTheory.Global.kummerExtension_pow_eq {y : kummerExtension K n Ω Δ} {a : K}
    (hy : (y : Ω) ^ n = algebraMap K Ω a) :
    y ^ n = algebraMap K (kummerExtension K n Ω Δ) a := by sorry
