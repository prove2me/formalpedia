-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_herm_move
-- name    : GlobalTheory.SW.Nbr.herm_move
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:09.07981+00:00
-- url     : https://prove2.me/theorems/168b19ab-6b02-4892-9366-07390143821b
-- title:
--   Nbr: herm move
-- statement:
--   The Nbr construction uses the herm move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L411-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L411-L418

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

theorem GlobalTheory.SW.Nbr.herm_move {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (x y : Fin n → E) :
    herm 1 (h *ᵥ x) (h *ᵥ y) = herm 1 x y := by sorry
