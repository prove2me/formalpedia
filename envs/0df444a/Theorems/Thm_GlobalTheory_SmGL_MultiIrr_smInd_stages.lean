-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_smInd_stages
-- name    : GlobalTheory.SmGL.MultiIrr.smInd_stages
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:03.906932+00:00
-- url     : https://prove2.me/theorems/2f6a8b16-bd8e-40ad-8ef9-547b2330e353
-- title:
--   Multi Irr: sm Ind stages
-- statement:
--   The Multi Irr construction uses the sm Ind stages property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L177-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L177-L262

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
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

theorem GlobalTheory.SmGL.MultiIrr.smInd_stages {P Q : Subgroup G} (hPQ : P ≤ Q) {P' : Subgroup H} (π : Q →* M × H) (j : H →* Q)
    (hj : Continuous fun x => (j x : G)) (hπj : ∀ x, π (j x) = (1, x))
    (hP : ∀ q : Q, (q : G) ∈ P ↔ (π q).2 ∈ P') {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P', ∃ w ∈ K, x = p * w) (D : M × H →* Fˣ)
    (hD : ∀ᶠ u in nhds (1 : H), D (1, u) = 1)
    (σ₀ : Representation F M V) (ρ : Representation F P' W) (σ : Representation F P U)
    (κ : V ⊗[F] W ≃ₗ[F] U)
    (hσ : ∀ (q : Q) (h1 : (q : G) ∈ P) (h2 : (π q).2 ∈ P') x, σ ⟨q, h1⟩ (κ x) =
      (D (π q) : F) • κ (TensorProduct.map (σ₀ (π q).1) (ρ ⟨_, h2⟩) x))
    (τ : Representation F Q (V ⊗[F] smoothPart (ind P' ρ)))
    (hτ : ∀ q x, τ q x = (D (π q) : F) • TensorProduct.map (σ₀ (π q).1) (smInd P' ρ (π q).2) x) :
    Nonempty ((smInd Q τ).Equiv (smInd P σ)) := by sorry
