-- Prove2me | Theorems.Thm_GlobalTheory_JR_DualLattice_box_open_compact
-- name    : GlobalTheory.JR.DualLattice.box_open_compact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:57.692494+00:00
-- url     : https://prove2.me/theorems/10a0d4e1-a395-4d87-937a-eccafa450dd7
-- title:
--   Dual Lattice: box open compact
-- statement:
--   The Dual Lattice construction uses the box open compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L56-L63

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

theorem GlobalTheory.JR.DualLattice.box_open_compact [IsUltrametricDist F] [LocallyCompactSpace F] [TopologicalSpace V]
    [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 < r) :
    IsOpen (box e r hr.le : Set V) ∧ IsCompact (box e r hr.le : Set V) := by sorry
