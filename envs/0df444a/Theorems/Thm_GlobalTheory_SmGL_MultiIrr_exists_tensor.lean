-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_tensor
-- name    : GlobalTheory.SmGL.MultiIrr.exists_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:46.579121+00:00
-- url     : https://prove2.me/theorems/78317080-9748-44ac-b67e-4c6d45548552
-- title:
--   Multi Irr: exists tensor
-- statement:
--   The Multi Irr construction uses the exists tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L146-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L146-L175

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
omit [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.SmGL.MultiIrr.exists_tensor {P : Subgroup H} (ρ : Representation F P W) {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P, ∃ w ∈ K, x = p * w) (f : H → V ⊗[F] W)
    (hf : ∀ (p : P) x, f (p * x) = (ρ p).lTensor V (f x))
    (hs : ∀ᶠ u in nhds (1 : H), ∀ x, f (x * u) = f x) :
    ∃ t : V ⊗[F] smoothPart (ind P ρ), ∀ x, (ev ρ x).lTensor V t = f x := by sorry
