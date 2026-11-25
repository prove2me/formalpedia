-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_splitsCompletely_kummerExtension_iff
-- name    : GroundTheory.Global.InfinitePlace.splitsCompletely_kummerExtension_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:15.384349+00:00
-- url     : https://prove2.me/theorems/3c226c39-bcbc-57bf-a3d6-c0863ad3ceb2
-- title:
--   Infinite Place: splits Completely kummer Extension iff
-- statement:
--   The Infinite Place construction uses the splits Completely kummer Extension iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L140-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L140-L152

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
variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω] {Δ : Subgroup Kˣ}
  [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]
open scoped NumberField.LiesOver

theorem GroundTheory.Global.InfinitePlace.splitsCompletely_kummerExtension_iff (v : NumberField.InfinitePlace K) :
    InfinitePlace.SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.Completion, x ^ n = algebraMap K v.Completion (a : K) := by sorry
