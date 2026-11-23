-- Prove2me | Theorems.Thm_GlobalTheory_sub_mem_lattice_of_weierstrassP_eq
-- name    : GlobalTheory.sub_mem_lattice_of_weierstrassP_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:08.999492+00:00
-- url     : https://prove2.me/theorems/316ba5f5-43cf-45bb-978c-e6a128ba1877
-- title:
--   Global Theory: sub mem lattice of weierstrass P eq
-- statement:
--   The Global Theory construction uses the sub mem lattice of weierstrass P eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L123-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L123-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.sub_mem_lattice_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : ℘[L] z = ℘[L] w) (h' : ℘'[L] z = ℘'[L] w) : z - w ∈ L.lattice := by sorry
