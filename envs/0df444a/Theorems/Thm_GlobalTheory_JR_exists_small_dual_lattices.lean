-- Prove2me | Theorems.Thm_GlobalTheory_JR_exists_small_dual_lattices
-- name    : GlobalTheory.JR.exists_small_dual_lattices
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:05.001575+00:00
-- url     : https://prove2.me/theorems/8cd7f410-cff8-4a5c-80f3-d708f2264efb
-- title:
--   JR: exists small dual lattices
-- statement:
--   The JR construction uses the exists small dual lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L103-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean#L103-L136

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
open GlobalTheory.JR.DualLattice

theorem GlobalTheory.JR.exists_small_dual_lattices : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → Continuous (fun p : V × V => ψ (β p.1 p.2)) ∧ (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, ψ (β x y) = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, ψ (β x y) = 1)) := by sorry
