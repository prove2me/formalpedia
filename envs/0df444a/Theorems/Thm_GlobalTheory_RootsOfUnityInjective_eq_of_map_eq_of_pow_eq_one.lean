-- Prove2me | Theorems.Thm_GlobalTheory_RootsOfUnityInjective_eq_of_map_eq_of_pow_eq_one
-- name    : GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:51.6626+00:00
-- url     : https://prove2.me/theorems/ba23019c-94e5-41de-8eee-119e041a8317
-- title:
--   Roots Of Unity Injective: eq of map eq of pow eq one
-- statement:
--   The Roots Of Unity Injective construction uses the eq of map eq of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqOfMapEqOfPowEqOne.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqOfMapEqOfPowEqOne.lean#L5-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootsOfUnityInjective

theorem GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one {R k : Type} [CommRing R] [IsDomain R] [CommRing k] [IsDomain k]
    (π : R →+* k) {N : ℕ} (hN : (N : k) ≠ 0) {u w : R} (hu : u ^ N = 1) (hw : w ^ N = 1)
    (h : π u = π w) : u = w := by sorry
