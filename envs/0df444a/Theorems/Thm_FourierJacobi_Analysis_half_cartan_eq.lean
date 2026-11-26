-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_half_cartan_eq
-- name    : FourierJacobi.Analysis.half_cartan_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:23:41.365777+00:00
-- url     : https://prove2.me/theorems/107df3ec-7751-4d23-9007-9268a8be5aa5
-- title:
--   Analysis: half cartan eq
-- statement:
--   The Analysis construction uses the half cartan eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L39-L44
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L39-L44

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.half_cartan_eq (r k j h c : ℤ) :
    (cartanIndices r k j h c).1 / 2 =
      entryMinimum r k j h - minorMinimum r k j h c := by sorry
