-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_smInd_iff
-- name    : GlobalTheory.SmGL.MultiIrr.isIrreducible_smInd_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:51.455654+00:00
-- url     : https://prove2.me/theorems/58808a18-457c-48b7-9495-ab64456e7643
-- title:
--   Multi Irr: is Irreducible sm Ind iff
-- statement:
--   The Multi Irr construction uses the is Irreducible sm Ind iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L71-L88

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

theorem GlobalTheory.SmGL.MultiIrr.isIrreducible_smInd_iff {P : Subgroup G} {Q : Subgroup H} {σ : Representation F P V}
    {τ : Representation F Q W} (φ : G ≃* H) (hφ : Continuous φ) (hφ' : Continuous φ.symm) (κ : V ≃ₗ[F] W)
    (hP : ∀ g, g ∈ P ↔ φ g ∈ Q) (h : ∀ (p : P) v, κ (σ p v) = τ ⟨φ p, (hP p).1 p.2⟩ (κ v)) :
    (smInd P σ).IsIrreducible ↔ (smInd Q τ).IsIrreducible := by sorry
