-- Prove2me | Theorems.Thm_GlobalTheory_JR_DualLattice_mem_box
-- name    : GlobalTheory.JR.DualLattice.mem_box
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:25:38.329802+00:00
-- url     : https://prove2.me/theorems/2e532fde-80dc-47f4-b657-42c37c81f815
-- title:
--   Dual Lattice: mem box
-- statement:
--   The Dual Lattice construction uses the mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L39-L40

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

theorem GlobalTheory.JR.DualLattice.mem_box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    x ∈ box e r hr ↔ ∀ i, ‖e.repr x i‖ ≤ r := by sorry
