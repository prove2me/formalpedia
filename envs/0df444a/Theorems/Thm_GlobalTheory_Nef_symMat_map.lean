-- Prove2me | Theorems.Thm_GlobalTheory_Nef_symMat_map
-- name    : GlobalTheory.Nef.symMat_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:37.818535+00:00
-- url     : https://prove2.me/theorems/c94c0599-4877-4c61-afcd-341a770eb4b8
-- title:
--   Nef: sym Mat map
-- statement:
--   The Nef construction uses the sym Mat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistAtOfNe.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistAtOfNe.lean#L25-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.symMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : (symMat m A).map f = symMat m (A.map f) := by sorry
