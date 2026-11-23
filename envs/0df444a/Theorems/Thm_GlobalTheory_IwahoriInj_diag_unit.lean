-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_diag_unit
-- name    : GlobalTheory.IwahoriInj.diag_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:44.094579+00:00
-- url     : https://prove2.me/theorems/78a17ab8-6d0b-42ff-a467-eb24fff810bf
-- title:
--   Iwahori Inj: diag unit
-- statement:
--   The Iwahori Inj construction uses the diag unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L327-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L327-L338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.IwahoriInj.diag_unit {f : n → n → ℤ} (hf : Chamber f) {p : GL n k} {i : n}
    (h1 : ∀ l, Deep (f i l) (p.val i l)) (h2 : ∀ l, Deep (f l i) ((p⁻¹).val l i)) :
    ¬ Deep 1 (p.val i i) := by sorry
