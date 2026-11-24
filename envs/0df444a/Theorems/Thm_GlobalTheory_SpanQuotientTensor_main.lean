-- Prove2me | Theorems.Thm_GlobalTheory_SpanQuotientTensor_main
-- name    : GlobalTheory.SpanQuotientTensor.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:15.981907+00:00
-- url     : https://prove2.me/theorems/6ddfc5b2-f7ed-4c92-b337-1e2d9532f07a
-- title:
--   Span Quotient Tensor: main
-- statement:
--   The Span Quotient Tensor construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanMkQOneTmul.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanMkQOneTmul.lean#L22-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanMkQOneTmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanQuotientTensor

theorem GlobalTheory.SpanQuotientTensor.main : (let d1 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (U →+* F) → Submodule F (TensorProduct LL F D) := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ ⨆ (c : U), LinearMap.range (LinearMap.baseChange F ((m : U → Module.End LL D) c) - (τ : U → F) c • LinearMap.id)); let d2 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [Algebra LL F] → (U →+* F) → Type := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ TensorProduct LL F D ⧸ d1 m F τ); let d3 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → TensorProduct LL F D →ₗ[F] d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ Submodule.mkQ (d1 m F τ)); let d4 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → D → d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (x : D) ↦ (d3 m F τ : TensorProduct LL F D → d2 m F τ) ((1 : F) ⊗ₜ[LL] x)); ∀ {LL U D : Type} [inst : Field LL] [inst_1 : Field U] [inst_2 : AddCommGroup D] [inst_3 : Module LL D] (m : U →+* Module.End LL D) (F : Type) [inst_4 : Field F] [inst_5 : Algebra LL F] (τ : U →+* F), Submodule.span F (Set.range (d4 m F τ)) = ⊤) := by sorry
