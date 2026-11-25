-- Prove2me | Theorems.Thm_GroundTheory_Global_splitsCompletely_kummerExtension_iff
-- name    : GroundTheory.Global.splitsCompletely_kummerExtension_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:46.620736+00:00
-- url     : https://prove2.me/theorems/ea981957-d2c5-5d39-9d09-1b58dfa5372b
-- title:
--   Global: splits Completely kummer Extension iff
-- statement:
--   The Global construction uses the splits Completely kummer Extension iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean#L125-L136

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
open SemiLocal

theorem GroundTheory.Global.splitsCompletely_kummerExtension_iff (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) (a : K) := by sorry
