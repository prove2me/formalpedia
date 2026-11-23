-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_HasGJ_unique
-- name    : GlobalTheory.LGrp.HasGJ.unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:27.452815+00:00
-- url     : https://prove2.me/theorems/d330628b-5432-461a-a5f7-bcf0a09a398f
-- title:
--   Has GJ: unique
-- statement:
--   The Has GJ construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L270-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L270-L271

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

theorem GlobalTheory.LGrp.HasGJ.unique {R S : RatFunc ℂ} (h : HasGJ μ Ξ c R) (h' : HasGJ μ Ξ c S) : R = S := by sorry
