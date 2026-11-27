-- Prove2me | Theorems.Thm_GroundTheory_Global_finrank_kummerExtension
-- name    : GroundTheory.Global.finrank_kummerExtension
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:55:41.649287+00:00
-- url     : https://prove2.me/theorems/470ac912-90b4-5f9b-b087-7cad3c671569
-- title:
--   Global: finrank kummer Extension
-- statement:
--   The Global construction uses the finrank kummer Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Degree.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Degree.lean#L126-L129

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.ProfCoh IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ)
variable [IsSepClosed Ω]
variable [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]

theorem GroundTheory.Global.finrank_kummerExtension :
    Module.finrank K (kummerExtension K n Ω Δ) = Nat.card (Δ ⧸ (unitsPow K n).subgroupOf Δ) := by sorry
