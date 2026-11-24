-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Sum_add_period
-- name    : GlobalTheory.AnArc.Sum_add_period
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:28.186725+00:00
-- url     : https://prove2.me/theorems/26dd78cf-dd4e-4b96-a3f6-331d488a5d09
-- title:
--   An Arc: Sum add period
-- statement:
--   The An Arc construction uses the Sum add period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L81-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
open AlgebraicGeometry CategoryTheory Limits
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O)

theorem GlobalTheory.AnArc.Sum_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) :
    A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v := by sorry
