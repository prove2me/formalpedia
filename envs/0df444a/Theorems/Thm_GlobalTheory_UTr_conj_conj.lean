-- Prove2me | Theorems.Thm_GlobalTheory_UTr_conj_conj
-- name    : GlobalTheory.UTr.conj_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:41.53718+00:00
-- url     : https://prove2.me/theorems/5f429d1d-c2ed-49ed-9ae8-5c23d8275efd
-- title:
--   UTr: conj conj
-- statement:
--   The UTr construction uses the conj conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L186-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L186-L214

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

theorem GlobalTheory.UTr.conj_conj (hs : ∀ b, s (s b) = b)
    (z : _root_.GlobalTheory.UTr.Alg P) :
    _root_.GlobalTheory.UTr.conj P (_root_.GlobalTheory.UTr.conj P z) = z := by sorry
