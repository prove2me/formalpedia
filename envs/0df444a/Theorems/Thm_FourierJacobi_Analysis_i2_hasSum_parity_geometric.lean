-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i2_hasSum_parity_geometric
-- name    : FourierJacobi.Analysis.i2_hasSum_parity_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:58:05.873343+00:00
-- url     : https://prove2.me/theorems/a81b999c-b38c-5246-be0b-5dedb081535b
-- title:
--   Analysis: i2 has Sum parity geometric
-- statement:
--   The Analysis construction uses the i2 has Sum parity geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L54-L69
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Convergence.lean#L54-L69

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis

theorem FourierJacobi.Analysis.i2_hasSum_parity_geometric (C z a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    HasSum (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2)
      (C * (1 + z) * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹) := by sorry
