-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_fifty_rows_split
-- name    : FourierJacobi.Analysis.fifty_rows_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:09:25.431086+00:00
-- url     : https://prove2.me/theorems/b2311020-f86a-582c-a0ad-30fbb1ea2f8b
-- title:
--   Analysis: fifty rows split
-- statement:
--   The Analysis construction uses the fifty rows split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L33-L40
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L33-L40

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

theorem FourierJacobi.Analysis.fifty_rows_split (f : Fin 50 → ℂ) :
    (∑ i : Fin 10, f (i.castLE (by decide))) +
    (∑ i : Fin 15, f ⟨10 + i.val, by omega⟩) +
    (∑ i : Fin 25, f ⟨25 + i.val, by omega⟩) = ∑ i : Fin 50, f i := by sorry
