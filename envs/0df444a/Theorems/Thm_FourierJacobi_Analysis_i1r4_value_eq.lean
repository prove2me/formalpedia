-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1r4_value_eq
-- name    : FourierJacobi.Analysis.i1r4_value_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:57:00.675395+00:00
-- url     : https://prove2.me/theorems/353be40b-e46f-473f-8ac4-9e3f1d6d3738
-- title:
--   Analysis: i1r4 value eq
-- statement:
--   The Analysis construction uses the i1r4 value eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L414-L428
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L414-L428

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Analysis.i1r4_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) = (regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by sorry
