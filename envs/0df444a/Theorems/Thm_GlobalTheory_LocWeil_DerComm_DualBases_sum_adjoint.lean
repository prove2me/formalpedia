-- Prove2me | Theorems.Thm_GlobalTheory_LocWeil_DerComm_DualBases_sum_adjoint
-- name    : GlobalTheory.LocWeil.DerComm.DualBases.sum_adjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:30.365769+00:00
-- url     : https://prove2.me/theorems/4aa3d442-a134-41ad-a184-eb1bd989f939
-- title:
--   Dual Bases: sum adjoint
-- statement:
--   The Dual Bases construction uses the sum adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L171-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L171-L180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
variable {S U : Type} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)
variable {β b b'}

theorem GlobalTheory.LocWeil.DerComm.DualBases.sum_adjoint (h : DualBases β b b') {M : Type} [AddCommGroup M] [Module ℝ M] (B : U →ₗ[ℝ] U →ₗ[ℝ] M)
    (g g' : U → U) (hg : ∀ x y, β (g' x) y = β x (g y)) : ∑ i, B (g (b i)) (b' i) = ∑ i, B (b i) (g' (b' i)) := by sorry
