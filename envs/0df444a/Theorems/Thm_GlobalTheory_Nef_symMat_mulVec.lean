-- Prove2me | Theorems.Thm_GlobalTheory_Nef_symMat_mulVec
-- name    : GlobalTheory.Nef.symMat_mulVec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:52.673938+00:00
-- url     : https://prove2.me/theorems/43ea66bd-f9b6-4e8f-b8d4-ee0a84344b6a
-- title:
--   Nef: sym Mat mul Vec
-- statement:
--   The Nef construction uses the sym Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistAtOfNe.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistAtOfNe.lean#L16-L23

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

theorem GlobalTheory.Nef.symMat_mulVec {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R)
    (p : Fin (m + 1) → R) :
    (symMat m A).mulVec p = fun a =>
      (∑ i : Fin (m + 1), C (p i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a := by sorry
