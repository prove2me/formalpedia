-- Prove2me | Theorems.Thm_GlobalTheory_UTr_evalMat_eq_mulMat
-- name    : GlobalTheory.UTr.evalMat_eq_mulMat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:14.100532+00:00
-- url     : https://prove2.me/theorems/b69e0dd9-6450-47d6-85c9-0deb2b421b31
-- title:
--   UTr: eval Mat eq mul Mat
-- statement:
--   The UTr construction uses the eval Mat eq mul Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L496-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L496-L497

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
variable {x x' : Alg P}

theorem GlobalTheory.UTr.evalMat_eq_mulMat {g : Matrix n n B} (hg : aeval g P.1 = 0) {i : Alg P ≃ₗ[B] (n → B)} (hi : mulMat i (root P) = g)
    (z : Alg P) : evalMat P g hg z = mulMat i z := by sorry
