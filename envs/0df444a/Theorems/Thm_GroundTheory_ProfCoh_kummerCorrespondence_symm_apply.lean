-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_kummerCorrespondence_symm_apply
-- name    : GroundTheory.ProfCoh.kummerCorrespondence_symm_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:59.273724+00:00
-- url     : https://prove2.me/theorems/f76ce1b0-5c65-4852-816f-77e39effea8c
-- title:
--   Prof Coh: kummer Correspondence symm apply
-- statement:
--   The Prof Coh construction uses the kummer Correspondence symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L394-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerCorrespondence.lean#L394-L397

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

theorem GroundTheory.ProfCoh.kummerCorrespondence_symm_apply [IsSepClosed Ω]
    (E : {E : IntermediateField K Ω //
      IsGalois K E ∧ IsMulCommutative Gal(E/K) ∧ Monoid.exponent Gal(E/K) ∣ n}) :
    (kummerCorrespondence K n Ω).symm E = kummerGroup K n E.1 := by sorry

attribute [defeq] GroundTheory.ProfCoh.kummerCorrespondence_symm_apply
