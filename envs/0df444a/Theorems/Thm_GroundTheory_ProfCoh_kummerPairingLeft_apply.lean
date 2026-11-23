-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_kummerPairingLeft_apply
-- name    : GroundTheory.ProfCoh.kummerPairingLeft_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:57.391412+00:00
-- url     : https://prove2.me/theorems/a4aa39e0-fd9d-42de-b25d-57b7a9415164
-- title:
--   Prof Coh: kummer Pairing Left apply
-- statement:
--   The Prof Coh construction uses the kummer Pairing Left apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L250-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L250-L251

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

theorem GroundTheory.ProfCoh.kummerPairingLeft_apply (σ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairingLeft K n L σ x = kummerPairing K n L σ x := by sorry

attribute [defeq] GroundTheory.ProfCoh.kummerPairingLeft_apply
