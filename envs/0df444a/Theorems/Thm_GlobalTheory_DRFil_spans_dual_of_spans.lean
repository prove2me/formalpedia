-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_spans_dual_of_spans
-- name    : GlobalTheory.DRFil.spans_dual_of_spans
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:56.143502+00:00
-- url     : https://prove2.me/theorems/cbf34cd2-42ce-4d79-b59c-9d0ce43f9a22
-- title:
--   DRFil: spans dual of spans
-- statement:
--   The DRFil construction uses the spans dual of spans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean#L281-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean#L281-L283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem GlobalTheory.DRFil.spans_dual_of_spans : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] [FiniteDimensional LL V'] (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL), IsField F → (∀ g x y, β (ρ g x) (ρ' g y) = β x y) → Function.Bijective β.flip → Spans PD ρ → Spans PD ρ' := by sorry
