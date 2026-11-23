-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_kummerPairingRight_apply
-- name    : GroundTheory.ProfCoh.kummerPairingRight_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:54.541202+00:00
-- url     : https://prove2.me/theorems/88fef681-efe7-4b0d-804d-596554a26595
-- title:
--   Prof Coh: kummer Pairing Right apply
-- statement:
--   The Prof Coh construction uses the kummer Pairing Right apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L253-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L253-L254

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]
variable {K n L}
variable (K n L)

theorem GroundTheory.ProfCoh.kummerPairingRight_apply (x : kummerGroup K n L) (σ : Gal(L/K)) :
    kummerPairingRight K n L x σ = kummerPairing K n L σ x := by sorry

attribute [defeq] GroundTheory.ProfCoh.kummerPairingRight_apply
