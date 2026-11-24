-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_indep_of_linearIndependent_DdRE
-- name    : GlobalTheory.DRFil.indep_of_linearIndependent_DdRE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:27.935091+00:00
-- url     : https://prove2.me/theorems/0b91fa4a-80b0-4a1d-b27d-578f712c8283
-- title:
--   DRFil: indep of linear Independent Dd RE
-- statement:
--   The DRFil construction uses the indep of linear Independent Dd RE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOfLinearIndependentDdRE.lean#L154-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOfLinearIndependentDdRE.lean#L154-L292

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOfLinearIndependentDdRE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
open GlobalTheory GlobalTheory.DRFil

theorem GlobalTheory.DRFil.indep_of_linearIndependent_DdRE {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B]
    [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F]
    [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    {ι : Type} [Fintype ι] (d : ι → V ⊗[Qp] F) (hF : IsField F) (hd : ∀ i, d i ∈ DdRE PD ρ τ)
    (hind : LinearIndependent LL d) (r : ι → LL ⊗[Qp] F)
    (hr : ∑ i, sm Qp F LL V (r i) (d i) = 0) : ∀ i, idem F τ * r i = 0 := by sorry
