-- Prove2me | Theorems.Thm_GlobalTheory_mk_addMonoidHom_le_of_surjective_of_injective
-- name    : GlobalTheory.mk_addMonoidHom_le_of_surjective_of_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:19.303803+00:00
-- url     : https://prove2.me/theorems/5bef9947-2aab-4a03-b75e-11408fe603b3
-- title:
--   Global Theory: mk add Monoid Hom le of surjective of injective
-- statement:
--   The Global Theory construction uses the mk add Monoid Hom le of surjective of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L7-L14

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

theorem GlobalTheory.mk_addMonoidHom_le_of_surjective_of_injective {A A' X Y : Type} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup X] [AddCommGroup Y] (f : A →+ A') (hf : Surjective f)
    (ι : X →+ Y) (hι : Injective ι) : #(A' →+ X) ≤ #(A →+ Y) := by sorry
