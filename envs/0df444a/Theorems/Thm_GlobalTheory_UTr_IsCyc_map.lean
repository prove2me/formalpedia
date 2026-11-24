-- Prove2me | Theorems.Thm_GlobalTheory_UTr_IsCyc_map
-- name    : GlobalTheory.UTr.IsCyc.map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:09.632365+00:00
-- url     : https://prove2.me/theorems/353a16ca-b5eb-4339-9cef-b60eaa5c8089
-- title:
--   Is Cyc: map
-- statement:
--   The Is Cyc construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L528-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L528-L558

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

theorem GlobalTheory.UTr.IsCyc.map {g : Matrix n n B} (h : IsCyc P g) (φ : B →+* B') {Q : Csr s'} (hQ : Q.1 = P.1.map φ) :
    IsCyc Q (g.map φ) := by sorry
