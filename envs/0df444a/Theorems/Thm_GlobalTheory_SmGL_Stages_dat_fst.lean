-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_dat_fst
-- name    : GlobalTheory.SmGL.Stages.dat_fst
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:13:38.148102+00:00
-- url     : https://prove2.me/theorems/3f03f128-8a97-46b9-b1fd-f651e74455b9
-- title:
--   Stages: dat fst
-- statement:
--   The Stages construction uses the dat fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L280-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L280-L289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

theorem GlobalTheory.SmGL.Stages.dat_fst (e : a ⊕ b ≃ n) (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (q : parab k (two e)) (y : V₁ ⊗[ℂ] V₂) :
    TensorProduct.comm ℂ V₁ V₂ (dat e (extTensor π₁ π₂) q y) =
      TensorProduct.map (π₂ (pr e q).2) (tauFst e π₁ q) (TensorProduct.comm ℂ V₁ V₂ y) := by sorry
