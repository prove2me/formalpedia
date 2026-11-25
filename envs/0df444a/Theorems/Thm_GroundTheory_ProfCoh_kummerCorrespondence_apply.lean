-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_kummerCorrespondence_apply
-- name    : GroundTheory.ProfCoh.kummerCorrespondence_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:19.558376+00:00
-- url     : https://prove2.me/theorems/b908a908-824b-4ea9-b633-509fbd0cd87f
-- title:
--   Prof Coh: kummer Correspondence apply
-- statement:
--   The Prof Coh construction uses the kummer Correspondence apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L391-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L391-L392

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

theorem GroundTheory.ProfCoh.kummerCorrespondence_apply [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    (kummerCorrespondence K n Ω Δ : IntermediateField K Ω) = kummerField K n Ω Δ := by sorry

attribute [defeq] GroundTheory.ProfCoh.kummerCorrespondence_apply
