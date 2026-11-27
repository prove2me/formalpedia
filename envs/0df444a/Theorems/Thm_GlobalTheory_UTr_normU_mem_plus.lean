-- Prove2me | Theorems.Thm_GlobalTheory_UTr_normU_mem_plus
-- name    : GlobalTheory.UTr.normU_mem_plus
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:34.349955+00:00
-- url     : https://prove2.me/theorems/20e8c0cb-fe99-5180-a034-772c4b8e77ee
-- title:
--   UTr: norm U mem plus
-- statement:
--   The UTr construction uses the norm U mem plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L247-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L247-L251

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
open Polynomial Matrix
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : _root_.GlobalTheory.UTr.Csr s)

theorem GlobalTheory.UTr.normU_mem_plus (hs : ∀ b, s (s b) = b)
    (z : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
    _root_.GlobalTheory.UTr.normU P z ∈ _root_.GlobalTheory.UTr.plus P := by sorry
