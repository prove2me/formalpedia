-- Prove2me | Theorems.Thm_GlobalTheory_UTr_eq_evalMat
-- name    : GlobalTheory.UTr.eq_evalMat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:04.955803+00:00
-- url     : https://prove2.me/theorems/9881d759-250d-4089-94ef-7bb9ff095c99
-- title:
--   UTr: eq eval Mat
-- statement:
--   The UTr construction uses the eq eval Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L354-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L354-L357

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
variable {P}

theorem GlobalTheory.UTr.eq_evalMat {g : Matrix n n B} (hg : aeval g P.1 = 0) (f : Alg P →ₐ[B] Matrix n n B) (hf : f (root P) = g)
    (z : Alg P) : f z = evalMat P g hg z := by sorry
