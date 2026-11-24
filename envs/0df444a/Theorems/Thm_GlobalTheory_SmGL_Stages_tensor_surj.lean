-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_tensor_surj
-- name    : GlobalTheory.SmGL.Stages.tensor_surj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:06.187811+00:00
-- url     : https://prove2.me/theorems/3b8b4134-9da8-40a9-9882-e346c594600e
-- title:
--   Stages: tensor surj
-- statement:
--   The Stages construction uses the tensor surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L91-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L91-L120

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
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]

theorem GlobalTheory.SmGL.Stages.tensor_surj {P : Subgroup M} (σ : Representation F P W) {K : Set M} (hK : IsCompact K)
    (hPK : ∀ m, ∃ p : P, ∃ c ∈ K, m = p * c) (ψ : M → W ⊗[F] X)
    (h1 : ∀ (p : P) m, ψ (p * m) = (σ p).rTensor X (ψ m))
    (h2 : ∀ᶠ u in 𝓝 (1 : M), ∀ x, ψ (x * u) = ψ x) :
    ∃ y : smoothPart (ind P σ) ⊗[F] X, ∀ m, (evalAt σ m).rTensor X y = ψ m := by sorry
