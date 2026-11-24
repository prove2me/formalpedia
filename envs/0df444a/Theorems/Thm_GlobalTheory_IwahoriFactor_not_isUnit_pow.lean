-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriFactor_not_isUnit_pow
-- name    : GlobalTheory.IwahoriFactor.not_isUnit_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:04.712808+00:00
-- url     : https://prove2.me/theorems/a23e23b5-5060-4ec2-8ecf-e2972633c85a
-- title:
--   Iwahori Factor: not is Unit pow
-- statement:
--   The Iwahori Factor construction uses the not is Unit pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L247-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L247-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor

theorem GlobalTheory.IwahoriFactor.not_isUnit_pow {O : Type} [CommRing O] {ϖ : O} (hϖ : Irreducible ϖ) {s : ℕ} (hs : 1 ≤ s) :
    ¬ IsUnit (ϖ ^ s) := by sorry
