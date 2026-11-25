-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_multiProd
-- name    : GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:19.522266+00:00
-- url     : https://prove2.me/theorems/8de557ee-1fd8-43d3-b2a2-b93ec800acc7
-- title:
--   Multi Irr: is Irreducible multi Prod
-- statement:
--   The Multi Irr construction uses the is Irreducible multi Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L484-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L484-L496

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

theorem GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {s : ℕ} :
    ∀ {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {n : Type} [Fintype n] [DecidableEq n]
    (e : (Σ i, m i) ≃ n) {X : Fin s → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {σ : ∀ i, Representation ℂ (GL (m i) k) (X i)}, (∀ i, IsSmooth (σ i)) → (∀ i, (σ i).IsIrreducible) →
    (∀ i, IsUnitarisable (σ i)) → (multiProd e σ).IsIrreducible := by sorry
