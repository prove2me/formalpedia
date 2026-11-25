-- Prove2me | Theorems.Thm_GlobalTheory_HolomorphicArc_isHolTo_halfPlane_mono
-- name    : GlobalTheory.HolomorphicArc.isHolTo_halfPlane_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:17.35685+00:00
-- url     : https://prove2.me/theorems/12eebb38-ef0c-58ba-8fef-8ac12d81ff43
-- title:
--   Holomorphic Arc: is Hol To half Plane mono
-- statement:
--   The Holomorphic Arc construction uses the is Hol To half Plane mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHolToHalfPlaneMono.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHolToHalfPlaneMono.lean#L46-L54

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem GlobalTheory.HolomorphicArc.isHolTo_halfPlane_mono {X : Scheme.{0}} {y : ℂ → (Sp ℂ ⟶ X)} {T T' : ℝ} (h : T ≤ T')
    (hol : IsHolTo {w : ℂ | T < w.im} y) : IsHolTo {w : ℂ | T' < w.im} y := by sorry
