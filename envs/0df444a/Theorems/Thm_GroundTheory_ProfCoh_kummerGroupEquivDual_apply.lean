-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_kummerGroupEquivDual_apply
-- name    : GroundTheory.ProfCoh.kummerGroupEquivDual_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:24.832436+00:00
-- url     : https://prove2.me/theorems/b05a73cc-0b8f-465d-9c6b-60e6c1dd202e
-- title:
--   Prof Coh: kummer Group Equiv Dual apply
-- statement:
--   The Prof Coh construction uses the kummer Group Equiv Dual apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerFinite.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerFinite.lean#L185-L187

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
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

theorem GroundTheory.ProfCoh.kummerGroupEquivDual_apply [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) (x : kummerGroup K n L)
    (σ : Gal(L/K)) : kummerGroupEquivDual K n L hexp x σ = kummerPairing K n L σ x := by sorry

attribute [defeq] GroundTheory.ProfCoh.kummerGroupEquivDual_apply
