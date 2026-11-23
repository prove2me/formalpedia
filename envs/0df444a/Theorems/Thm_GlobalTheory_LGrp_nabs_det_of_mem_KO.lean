-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_nabs_det_of_mem_KO
-- name    : GlobalTheory.LGrp.nabs_det_of_mem_KO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:33.093806+00:00
-- url     : https://prove2.me/theorems/06a9a697-a233-4930-9b40-1460c262f8e9
-- title:
--   LGrp: nabs det of mem KO
-- statement:
--   The LGrp construction uses the nabs det of mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L303-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L303-L314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
open MeasureTheory Matrix
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
omit [MeasurableSpace (GL n k)]

theorem GlobalTheory.LGrp.nabs_det_of_mem_KO {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by sorry
