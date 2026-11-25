-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_hermC_eq
-- name    : GlobalTheory.PerMove.hermC_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:04.288419+00:00
-- url     : https://prove2.me/theorems/31a17fd7-1720-4ba1-8e08-0b4760b798e2
-- title:
--   Per Move: herm C eq
-- statement:
--   The Per Move construction uses the herm C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L51-L53

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.PerMove.hermC_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    FD.hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by sorry
