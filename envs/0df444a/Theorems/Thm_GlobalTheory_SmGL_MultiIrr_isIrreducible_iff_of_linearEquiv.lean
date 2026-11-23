-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_linearEquiv
-- name    : GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:33.412783+00:00
-- url     : https://prove2.me/theorems/87b9745f-3283-4b41-8408-05cbbf40cacd
-- title:
--   Multi Irr: is Irreducible iff of linear Equiv
-- statement:
--   The Multi Irr construction uses the is Irreducible iff of linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L19-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L19-L38

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

theorem GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv {ρ : Representation F G V} {σ : Representation F H W} (φ : G → H)
    (hφ : Function.Surjective φ) (κ : V ≃ₗ[F] W) (h : ∀ g v, κ (ρ g v) = σ (φ g) (κ v)) :
    ρ.IsIrreducible ↔ σ.IsIrreducible := by sorry
