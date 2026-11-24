-- Prove2me | Theorems.Thm_GlobalTheory_UTr_IsCyc_aeval_eq_zero
-- name    : GlobalTheory.UTr.IsCyc.aeval_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:24.316571+00:00
-- url     : https://prove2.me/theorems/9d148195-26fc-479c-98b2-597b16b82421
-- title:
--   Is Cyc: aeval eq zero
-- statement:
--   The Is Cyc construction uses the aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L493-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean#L493-L494

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

theorem GlobalTheory.UTr.IsCyc.aeval_eq_zero {g : Matrix n n B} (h : IsCyc P g) : aeval g P.1 = 0 := by sorry
