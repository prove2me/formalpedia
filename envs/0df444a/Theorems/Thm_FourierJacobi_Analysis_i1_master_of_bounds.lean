-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_master_of_bounds
-- name    : FourierJacobi.Analysis.i1_master_of_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:29:51.657383+00:00
-- url     : https://prove2.me/theorems/811a170b-9de3-5daf-b84a-2b63b3e345db
-- title:
--   Analysis: i1 master of bounds
-- statement:
--   Natural real damping and unitary monomial hypotheses. The strict
--   inequality T*t < ‖δ‖ covers damped endpoint and undamped interior cases.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1185-L1197
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean#L1185-L1197

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

theorem FourierJacobi.Analysis.i1_master_of_bounds (q t T : ℝ) (d U V : ℂ)
    (hqt : q*t^2=1) (ht0 : 0<t) (ht1 : t<1) (hT0 : 0≤T) (hT1 : T≤1)
    (hdlo : t≤‖d‖) (hdhi : ‖d‖≤1) (hstrict : T*t<‖d‖)
    (hU : ‖U‖=1) (hV : ‖V‖=1) :
    Summable (fun p : LatticeIndex => ‖masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1 p‖) ∧
    HasSum (masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1)
      (∑ i : Fin 15, regionTerms (t:ℂ) d ((T:ℂ)*U) ((T:ℂ)*V) ⟨10+i.val, by omega⟩) := by sorry
