-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_adjoin_nthRoots_eq_top
-- name    : GroundTheory.ProfCoh.adjoin_nthRoots_eq_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:25.951703+00:00
-- url     : https://prove2.me/theorems/04180995-9379-45a3-97c7-635c8f0f8822
-- title:
--   Prof Coh: adjoin nth Roots eq top
-- statement:
--   The Prof Coh construction uses the adjoin nth Roots eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerFinite.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerFinite.lean#L206-L212

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

theorem GroundTheory.ProfCoh.adjoin_nthRoots_eq_top [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    IntermediateField.adjoin K {α : L | α ≠ 0 ∧ α ^ n ∈ Set.range (algebraMap K L)} = ⊤ := by sorry
