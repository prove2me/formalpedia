-- Prove2me | Theorems.Thm_GlobalTheory_T_period_data_comparison
-- name    : GlobalTheory.T.period_data_comparison
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:55:13.825802+00:00
-- url     : https://prove2.me/theorems/fd8f5f81-35a9-4fa1-b763-f51ead3658d6
-- title:
--   T: period data comparison
-- statement:
--   The T construction uses the period data comparison property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PeriodDataComparisonStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PeriodDataComparisonStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparisonStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.period_data_comparison : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) (W W' : Matrix (Fin n) (Fin n) BdR), W * W' = 1 → (∀ i j, W i j ∈ PD.Fil 0) → (∀ i j, W' i j ∈ PD.Fil 0) → (∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a → a = 0 := by sorry
