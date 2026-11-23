-- Prove2me | Theorems.Thm_GlobalTheory_JR_DualLattice_box_eq
-- name    : GlobalTheory.JR.DualLattice.box_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:00.083239+00:00
-- url     : https://prove2.me/theorems/aaa83ba6-1c8a-4546-bef5-0ed78aac1c93
-- title:
--   Dual Lattice: box eq
-- statement:
--   The Dual Lattice construction uses the box eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L49-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
variable {F : Type} [NontriviallyNormedField F]
variable {V : Type} [AddCommGroup V] [Module F V]

theorem GlobalTheory.JR.DualLattice.box_eq [IsUltrametricDist F] [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) :
    (box e r hr : Set V) = coordHomeo e ⁻¹' Metric.closedBall 0 r := by sorry
