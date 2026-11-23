-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_coeff_FSum
-- name    : GlobalTheory.AnArc.coeff_FSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:00.799946+00:00
-- url     : https://prove2.me/theorems/9302a485-6951-467a-b3ee-9255cd562da9
-- title:
--   An Arc: coeff FSum
-- statement:
--   The An Arc construction uses the coeff FSum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L606-L607
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L606-L607

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.coeff_FSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) (n : ℤ) :
    (A.FSum j α th v).coeff n = ∑ μ ∈ A.level j α n, A.term j α th μ v := by sorry
