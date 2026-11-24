-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_products_irreducible
-- name    : GlobalTheory.SmGL.MultiIrr.products_irreducible
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:13.49792+00:00
-- url     : https://prove2.me/theorems/cac8fb11-431a-4c51-8c8e-89ecb1aafcd8
-- title:
--   Multi Irr: products irreducible
-- statement:
--   The Multi Irr construction uses the products irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L500-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L500-L516

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr

theorem GlobalTheory.SmGL.MultiIrr.products_irreducible (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (∀ (s : ℕ) (d : Fin s → ℕ) (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, Fin (d a)) ≃ n)
      (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
      (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
      (∀ a, IsSmooth (σ a)) → (∀ a, (σ a).IsIrreducible) → (∀ a, IsUnitarisable (σ a)) →
      IsSmooth (multiProd e σ) ∧ (multiProd e σ).IsIrreducible ∧ IsUnitarisable (multiProd e σ)) ∧
    ∀ (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
      (e : a ⊕ b ≃ n) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL a k) V) (π₂ : Representation ℂ (GL b k) W),
      IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
      IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
      (ind₂ e (extTensor π₁ π₂)).IsIrreducible ∧ (ind₂Lower e (extTensor π₁ π₂)).IsIrreducible := by sorry
