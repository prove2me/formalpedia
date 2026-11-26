-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1Raw_eq_shell
-- name    : FourierJacobi.Analysis.i1Raw_eq_shell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:23:16.394604+00:00
-- url     : https://prove2.me/theorems/c1076c17-53f7-4f89-8115-4921437b7f30
-- title:
--   Analysis: i1 Raw eq shell
-- statement:
--   The Analysis construction uses the i1 Raw eq shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L28-L40
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L28-L40

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem FourierJacobi.Analysis.i1Raw_eq_shell (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q * t ^ 2 = 1) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    i1Raw t d U V T p c = shellCoeff q 1 * shellMonomial t d U V T 1 p c := by sorry
