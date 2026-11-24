-- Prove2me | Theorems.Thm_GlobalTheory_JacStagesExact_relJacMap_injective
-- name    : GlobalTheory.JacStagesExact.relJacMap_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:07.992368+00:00
-- url     : https://prove2.me/theorems/b127d7c5-6b41-4124-aa33-87cf5c2d18fc
-- title:
--   Jac Stages Exact: rel Jac Map injective
-- statement:
--   The Jac Stages Exact construction uses the rel Jac Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientRelativeJacquetBlockLevi.lean#L29-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientRelativeJacquetBlockLevi.lean#L29-L59

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

theorem GlobalTheory.JacStagesExact.relJacMap_injective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (relJacMap e' f) := by sorry
