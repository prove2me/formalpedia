-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_spans_dual
-- name    : GlobalTheory.DRFil.spans_dual
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:22.747215+00:00
-- url     : https://prove2.me/theorems/2febb37a-5854-4c3e-af34-fb86ec65410a
-- title:
--   DRFil: spans dual
-- statement:
--   The DRFil construction uses the spans dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean#L233-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean#L233-L277

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
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem GlobalTheory.DRFil.spans_dual [FiniteDimensional Qp LL] [CharZero Qp] [FiniteDimensional LL V]
    (ρ : Representation LL G V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by sorry
