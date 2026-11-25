-- Prove2me | Theorems.Thm_GlobalTheory_HolomorphicArc_map_nsmul_eq_pow
-- name    : GlobalTheory.HolomorphicArc.map_nsmul_eq_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:28.178026+00:00
-- url     : https://prove2.me/theorems/c7c18f7f-1849-40ae-bc8b-0f3d09f55136
-- title:
--   Holomorphic Arc: map nsmul eq pow
-- statement:
--   The Holomorphic Arc construction uses the map nsmul eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHolToHalfPlaneMono.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHolToHalfPlaneMono.lean#L13-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHolToHalfPlaneMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory GlobalTheory.HolomorphicArc

theorem GlobalTheory.HolomorphicArc.map_nsmul_eq_pow {L G : Type} [AddCommGroup L] [Group G] (f : L → G) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f (n • a) = f a ^ n := by sorry
