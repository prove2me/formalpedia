-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_move_inv
-- name    : GlobalTheory.SW.Nbr.move_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:51.953297+00:00
-- url     : https://prove2.me/theorems/dd16a581-cdaa-4065-a67d-c399fc851c8a
-- title:
--   Nbr: move inv
-- statement:
--   The Nbr construction uses the move inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L420-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L420-L422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.SW.Nbr.move_inv {h : Matrix (Fin n) (Fin n) E} (hh : h * ccT h = 1) {Λ Λ₁ : Lt E n}
    (hm : Moves h Λ Λ₁) : Moves (ccT h) Λ₁ Λ := by sorry
