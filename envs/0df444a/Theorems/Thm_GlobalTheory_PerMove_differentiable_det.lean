-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_differentiable_det
-- name    : GlobalTheory.PerMove.differentiable_det
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:55.204266+00:00
-- url     : https://prove2.me/theorems/44cf2fe5-07c1-49fb-9b2c-8b763a5e37bb
-- title:
--   Per Move: differentiable det
-- statement:
--   The Per Move construction uses the differentiable det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L17-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate

theorem GlobalTheory.PerMove.differentiable_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}
    (M : X → Matrix (Fin r) (Fin r) ℂ) (hM : ∀ a b, Differentiable ℂ fun x => M x a b) :
    Differentiable ℂ fun x => (M x).det := by sorry
