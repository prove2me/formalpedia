-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_relJacD_mk
-- name    : GlobalTheory.JacStages.relJacD_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:08.063953+00:00
-- url     : https://prove2.me/theorems/ae0cdbbf-1487-4299-be96-a7aa2c89c22a
-- title:
--   Jac Stages: rel Jac D mk
-- statement:
--   The Jac Stages construction uses the rel Jac D mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L46-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacStages
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
variable {k}

theorem GlobalTheory.JacStages.relJacD_mk (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJacD f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalfD k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmbD k f g) v) := by sorry
