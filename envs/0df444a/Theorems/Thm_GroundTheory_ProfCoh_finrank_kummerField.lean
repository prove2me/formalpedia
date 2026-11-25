-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finrank_kummerField
-- name    : GroundTheory.ProfCoh.finrank_kummerField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:31.733591+00:00
-- url     : https://prove2.me/theorems/98281007-fdbb-4749-9105-3cdfba39d319
-- title:
--   Prof Coh: finrank kummer Field
-- statement:
--   The Prof Coh construction uses the finrank kummer Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L365-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L365-L370

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]

theorem GroundTheory.ProfCoh.finrank_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) [Finite Δ] :
    Module.finrank K (kummerField K n Ω Δ) = Nat.card Δ := by sorry
