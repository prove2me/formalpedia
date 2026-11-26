-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_central_master
-- name    : FourierJacobi.Analysis.summable_norm_central_master
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:09:28.474725+00:00
-- url     : https://prove2.me/theorems/9510f428-b91a-51a4-a80f-251147d480fe
-- title:
--   Analysis: summable norm central master
-- statement:
--   The Analysis construction uses the summable norm central master property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L42-L49
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L42-L49

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.summable_norm_central_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q - 1 ≠ 0)
    (hq2 : q - 2 ≠ 0) (hqt : q * t ^ 2 = 1) (h : GeometricRange t d U V T)
    (r : Fin 3) : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T (r.val : ℤ) p‖) := by sorry
