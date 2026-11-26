-- Prove2me | Theorems.Thm_FriedCrossing_TorsionCore_jordan_cluster_torsion
-- name    : FriedCrossing.TorsionCore.jordan_cluster_torsion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:57.342748+00:00
-- url     : https://prove2.me/theorems/966da8f0-7376-4a6d-8be3-d320e9a723bc
-- title:
--   Torsion Core: jordan cluster torsion
-- statement:
--   Jordan J₂ cluster (C), Xw₂ = w₁ = d₀u, d₀w₂ = λ·Lu: τ(C^•(0), Γ_ϑ) = −(1+λ)/λ.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L104-L105
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L104-L105

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem FriedCrossing.TorsionCore.jordan_cluster_torsion (l : K) (hl : l ≠ 0) : refinedTorsion 1 l = -(1 + l) / l := by sorry
