-- Prove2me | Theorems.Thm_GlobalTheory_JacStagesExact_isSubquotient_relJacD
-- name    : GlobalTheory.JacStagesExact.isSubquotient_relJacD
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:14.061747+00:00
-- url     : https://prove2.me/theorems/6d954bd7-c46e-4109-a8a9-14264c0a8502
-- title:
--   Jac Stages Exact: is Subquotient rel Jac D
-- statement:
--   The Jac Stages Exact construction uses the is Subquotient rel Jac D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientRelativeJacquetBlockLevi.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientRelativeJacquetBlockLevi.lean#L61-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientRelativeJacquetBlockLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages GlobalTheory.InertSupp
open GlobalTheory GlobalTheory.JacStagesExact
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.JacStagesExact.isSubquotient_relJacD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by sorry
