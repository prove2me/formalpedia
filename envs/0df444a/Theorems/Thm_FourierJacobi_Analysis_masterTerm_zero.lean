-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
-- name    : FourierJacobi.Analysis.masterTerm_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:36.871743+00:00
-- url     : https://prove2.me/theorems/7df5abbe-1d29-41e3-b488-4ed14bd5a44c
-- title:
--   Analysis: master Term zero
-- statement:
--   The Analysis construction uses the master Term zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L66-L71
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L66-L71

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.masterTerm_zero (q t d U V T : ℂ) (p : LatticeIndex) :
    masterTerm q t d U V T 0 p =
      if p.2.2.2 = 0 then i0Shell t d U V T (p.1, p.2.1, p.2.2.1) else 0 := by sorry
