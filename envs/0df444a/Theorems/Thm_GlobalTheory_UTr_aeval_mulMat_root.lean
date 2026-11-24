-- Prove2me | Theorems.Thm_GlobalTheory_UTr_aeval_mulMat_root
-- name    : GlobalTheory.UTr.aeval_mulMat_root
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:11.085595+00:00
-- url     : https://prove2.me/theorems/20b6a1f6-fe28-4d78-84a6-019f4d189c7c
-- title:
--   UTr: aeval mul Mat root
-- statement:
--   The UTr construction uses the aeval mul Mat root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L472-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L472-L473

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : Csr s)
variable {n : Type} [Fintype n] [DecidableEq n]
variable {J : Matrix n n B}
variable {P}

theorem GlobalTheory.UTr.aeval_mulMat_root (i : Alg P ≃ₗ[B] (n → B)) : aeval (mulMat i (root P)) P.1 = 0 := by sorry
