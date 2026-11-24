-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_spans_dual_base
-- name    : GlobalTheory.DRFil.spans_dual_base
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:27.125919+00:00
-- url     : https://prove2.me/theorems/33180200-a501-41cb-98e1-b4d489fb3e66
-- title:
--   DRFil: spans dual base
-- statement:
--   The DRFil construction uses the spans dual base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean#L46-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean#L46-L202

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
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)

theorem GlobalTheory.DRFil.spans_dual_base {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V]
    (ρ : Representation Qp G V) {V' : Type} [AddCommGroup V'] [Module Qp V']
    (ρ' : Representation Qp G V') (β : V →ₗ[Qp] V' →ₗ[Qp] Qp) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by sorry
