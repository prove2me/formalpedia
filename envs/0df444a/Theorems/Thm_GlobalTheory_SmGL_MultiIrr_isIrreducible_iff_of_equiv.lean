-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_equiv
-- name    : GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:54.772382+00:00
-- url     : https://prove2.me/theorems/edf714bd-d41b-4b55-9ba2-5e4cf221b3ea
-- title:
--   Multi Irr: is Irreducible iff of equiv
-- statement:
--   The Multi Irr construction uses the is Irreducible iff of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L40-L43

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

theorem GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv {ρ : Representation F G V} {σ : Representation F G W} (E : ρ.Equiv σ) :
    ρ.IsIrreducible ↔ σ.IsIrreducible := by sorry
