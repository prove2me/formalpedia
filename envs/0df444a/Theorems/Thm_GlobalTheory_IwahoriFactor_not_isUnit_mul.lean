-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriFactor_not_isUnit_mul
-- name    : GlobalTheory.IwahoriFactor.not_isUnit_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:57.529842+00:00
-- url     : https://prove2.me/theorems/6471b48d-a0ae-49af-b616-b0fa8dabd3b4
-- title:
--   Iwahori Factor: not is Unit mul
-- statement:
--   The Iwahori Factor construction uses the not is Unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L210-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L210-L211

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
variable {O : Type} [CommRing O] {n : ℕ}

theorem GlobalTheory.IwahoriFactor.not_isUnit_mul {α β : O} (hβ : ¬ IsUnit β) : ¬ IsUnit (α * β) := by sorry
