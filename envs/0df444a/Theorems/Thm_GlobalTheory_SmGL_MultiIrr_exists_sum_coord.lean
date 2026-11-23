-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_sum_coord
-- name    : GlobalTheory.SmGL.MultiIrr.exists_sum_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:49.975559+00:00
-- url     : https://prove2.me/theorems/f8635f87-10f9-41f1-b229-b5cfd313e399
-- title:
--   Multi Irr: exists sum coord
-- statement:
--   The Multi Irr construction uses the exists sum coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L107-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L107-L128

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

theorem GlobalTheory.SmGL.MultiIrr.exists_sum_coord {ι : Type} (b : Module.Basis ι F V) (x : V ⊗[F] W) :
    ∃ s : Finset ι, (∀ i ∉ s, coord (b.coord i) W x = 0) ∧
      ∀ t : Finset ι, s ⊆ t → x = ∑ i ∈ t, b i ⊗ₜ coord (b.coord i) W x := by sorry
