-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1CellValue_sum_eq_regions
-- name    : FourierJacobi.Analysis.i1CellValue_sum_eq_regions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:09:21.150775+00:00
-- url     : https://prove2.me/theorems/266044e5-4ba4-42af-816e-c9a265b481cf
-- title:
--   Analysis: i1 Cell Value sum eq regions
-- statement:
--   The Analysis construction uses the i1 Cell Value sum eq regions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1134-L1148
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1134-L1148

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

theorem FourierJacobi.Analysis.i1CellValue_sum_eq_regions (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (∑ i : Fin 17, i1CellValue q t d U V T i) =
      ∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by sorry
