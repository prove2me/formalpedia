-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_centralLatticeCore_sum
-- name    : FourierJacobi.Analysis.centralLatticeCore_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:10.635629+00:00
-- url     : https://prove2.me/theorems/92d1207f-1f81-49e5-a6ca-143ca673fecf
-- title:
--   Analysis: central Lattice Core sum
-- statement:
--   The Analysis construction uses the central Lattice Core sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean#L18-L25
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean#L18-L25

import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.centralLatticeCore_sum (q : ℝ) (a b d : ℂ) (T : ℝ) :
    (∑ r : Fin 3, centralLatticeCore q a b d T r) = latticeCore q a b d T := by sorry
