-- Prove2me | Theorems.Thm_GlobalTheory_mk_lt_mk_addMonoidHom_zmod_prime
-- name    : GlobalTheory.mk_lt_mk_addMonoidHom_zmod_prime
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:51.812063+00:00
-- url     : https://prove2.me/theorems/3415e028-1283-4700-9262-9d4ad73fed9f
-- title:
--   Global Theory: mk lt mk add Monoid Hom zmod prime
-- statement:
--   The Global Theory construction uses the mk lt mk add Monoid Hom zmod prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L35-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L35-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory

theorem GlobalTheory.mk_lt_mk_addMonoidHom_zmod_prime (p : ℕ) [hp : Fact p.Prime] (V : Type) [AddCommGroup V]
    (hV : ∀ x : V, p • x = 0) [Infinite V] : #V < #(V →+ ZMod p) := by sorry
