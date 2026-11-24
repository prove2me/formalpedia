-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_exists_idem_mul_eq
-- name    : GlobalTheory.DRFil.exists_idem_mul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:13.343569+00:00
-- url     : https://prove2.me/theorems/3264b419-8f25-4e15-a0c8-ccecb91b7769
-- title:
--   DRFil: exists idem mul eq
-- statement:
--   The DRFil construction uses the exists idem mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOfLinearIndependentDdRE.lean#L103-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOfLinearIndependentDdRE.lean#L103-L127

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

theorem GlobalTheory.DRFil.exists_idem_mul_eq {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {F : Type} [CommRing F] [Algebra Qp F] [Algebra K F] [IsScalarTower Qp K F]
    (τ : K →ₐ[Qp] LL) {κ : Type} [Fintype κ] (l : κ → LL)
    (hl : ∀ a : LL, ∃ c : κ → K, a = ∑ j, τ (c j) * l j) (r : LL ⊗[Qp] F) :
    ∃ b : κ → F, idem F τ * r = idem F τ * ∑ j, l j ⊗ₜ[Qp] b j := by sorry
