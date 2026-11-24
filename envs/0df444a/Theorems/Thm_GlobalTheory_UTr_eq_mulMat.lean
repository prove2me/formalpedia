-- Prove2me | Theorems.Thm_GlobalTheory_UTr_eq_mulMat
-- name    : GlobalTheory.UTr.eq_mulMat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:58.473151+00:00
-- url     : https://prove2.me/theorems/d15a016a-94cc-4d93-bbad-27027d71ce1a
-- title:
--   UTr: eq mul Mat
-- statement:
--   The UTr construction uses the eq mul Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L466-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L466-L470

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

theorem GlobalTheory.UTr.eq_mulMat (i : Alg P ≃ₗ[B] (n → B)) {z : Alg P} {g : Matrix n n B} (h : ∀ y, g *ᵥ i y = i (z * y)) :
    g = mulMat i z := by sorry
