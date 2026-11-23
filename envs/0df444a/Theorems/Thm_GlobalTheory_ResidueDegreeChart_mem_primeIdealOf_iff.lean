-- Prove2me | Theorems.Thm_GlobalTheory_ResidueDegreeChart_mem_primeIdealOf_iff
-- name    : GlobalTheory.ResidueDegreeChart.mem_primeIdealOf_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:12.066866+00:00
-- url     : https://prove2.me/theorems/a03b92ff-e007-499b-bf27-409392ee9bde
-- title:
--   Residue Degree Chart: mem prime Ideal Of iff
-- statement:
--   The Residue Degree Chart construction uses the mem prime Ideal Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueDegreeEqInertiaDegAffineChart.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueDegreeEqInertiaDegAffineChart.lean#L41-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ResidueDegreeChart

theorem GlobalTheory.ResidueDegreeChart.mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by sorry
