-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finiteDimensional_kummerField
-- name    : GroundTheory.ProfCoh.finiteDimensional_kummerField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:15.402724+00:00
-- url     : https://prove2.me/theorems/b3faf336-cdd5-4eb8-bd7c-8e3b850af305
-- title:
--   Prof Coh: finite Dimensional kummer Field
-- statement:
--   The Prof Coh construction uses the finite Dimensional kummer Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L357-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L357-L363

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

theorem GroundTheory.ProfCoh.finiteDimensional_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n))
    [Finite Δ] : FiniteDimensional K (kummerField K n Ω Δ) := by sorry
