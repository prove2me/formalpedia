-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceDet_det_mul_conj
-- name    : GlobalTheory.CongruenceDet.det_mul_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:38.294146+00:00
-- url     : https://prove2.me/theorems/3bdb06c8-cd06-4ff8-879a-38548b52e6fb
-- title:
--   Congruence Det: det mul conj
-- statement:
--   The Congruence Det construction uses the det mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralDetSubOne.lean#L120-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralDetSubOne.lean#L120-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
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
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors

theorem GlobalTheory.CongruenceDet.det_mul_conj {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (G g : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (g *ᵥ x) (g *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    g.det * IsCMField.complexConj E g.det = 1 := by sorry
