-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_intertwiner_entry_derivative
-- name    : FourierJacobi.Analysis.intertwiner_entry_derivative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:00.745082+00:00
-- url     : https://prove2.me/theorems/3c56ea83-b09b-4c63-961a-011eff25cd1e
-- title:
--   Analysis: intertwiner entry derivative
-- statement:
--   The Analysis construction uses the intertwiner entry derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/IntertwinerDerivative.lean#L39-L60
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/IntertwinerDerivative.lean#L39-L60

import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Definitions.Def_FourierJacobi_Analysis_IntertwinerDerivative
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis

theorem FourierJacobi.Analysis.intertwiner_entry_derivative (q : ℝ) (hq : 1 < q) (i j : Fin 2) :
    HasDerivAt (fun s => intertwinerFamily q s i j)
      ((-2 * Real.log q / (q - 1)) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (1 / 2) := by sorry
