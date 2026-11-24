-- Prove2me | Theorems.Thm_GlobalTheory_JR_DualLattice_box_dual
-- name    : GlobalTheory.JR.DualLattice.box_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:49.684004+00:00
-- url     : https://prove2.me/theorems/322ef102-4f07-4fc8-a107-e779a7802765
-- title:
--   Dual Lattice: box dual
-- statement:
--   The Dual Lattice construction uses the box dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L65-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L65-L97

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

theorem GlobalTheory.JR.DualLattice.box_dual [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) {ι : Type} [Fintype ι]
    (e e' : Module.Basis ι F V) (B : V → V → F)
    (hB : ∀ x y, B x y = ∑ i, e.repr x i * e'.repr y i) (t : F) (ht : t ≠ 0) (y : V) :
    y ∈ box e' ‖t⁻¹‖ (norm_nonneg _) ↔ ∀ x ∈ box e ‖t‖ (norm_nonneg _), ψ (B x y) = 1 := by sorry
