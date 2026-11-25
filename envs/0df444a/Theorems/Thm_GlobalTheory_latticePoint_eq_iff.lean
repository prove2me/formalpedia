-- Prove2me | Theorems.Thm_GlobalTheory_latticePoint_eq_iff
-- name    : GlobalTheory.latticePoint_eq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:39.329869+00:00
-- url     : https://prove2.me/theorems/71d3031c-4f70-415f-a6ff-52531c30525e
-- title:
--   Global Theory: lattice Point eq iff
-- statement:
--   The Global Theory construction uses the lattice Point eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L287-L290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair WeierstrassCurve
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
open Filter PeriodPair WeierstrassCurve
open scoped Topology
variable (L : PeriodPair)

theorem GlobalTheory.latticePoint_eq_iff {z w : ℂ} :
    _root_.GlobalTheory.latticePoint L z = _root_.GlobalTheory.latticePoint L w ↔ z - w ∈ L.lattice := by sorry
