-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_finite_generators_kummerField
-- name    : GroundTheory.ProfCoh.exists_finite_generators_kummerField
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:43.669484+00:00
-- url     : https://prove2.me/theorems/8ff29bdc-5678-4839-b7eb-1faf882f6c3a
-- title:
--   Prof Coh: exists finite generators kummer Field
-- statement:
--   The Prof Coh construction uses the exists finite generators kummer Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L340-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L340-L355

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

theorem GroundTheory.ProfCoh.exists_finite_generators_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    ∃ r : Δ → Ω, (∀ x : Δ, ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ r x ^ n = algebraMap K Ω a) ∧
      kummerField K n Ω Δ = adjoin K (Set.range r) := by sorry
