-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_mul_diagonal_eq_neg_of_exp
-- name    : GlobalTheory.ClassFin.mul_diagonal_eq_neg_of_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:57.810352+00:00
-- url     : https://prove2.me/theorems/2e4432bd-bd04-4dcb-bcca-9b73623233fc
-- title:
--   Class Fin: mul diagonal eq neg of exp
-- statement:
--   The Class Fin construction uses the mul diagonal eq neg of exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MulLogEqNegLogMul.lean#L8-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MulLogEqNegLogMul.lean#L8-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin

theorem GlobalTheory.ClassFin.mul_diagonal_eq_neg_of_exp {ι : Type} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) (d d' : ι → ℝ)
    (h : diagonal (fun i => (Real.exp (d' i) : ℂ)) * y * diagonal (fun i => (Real.exp (d i) : ℂ)) = y) :
    y * diagonal (fun i => (d i : ℂ)) = -(diagonal (fun i => (d' i : ℂ)) * y) := by sorry
