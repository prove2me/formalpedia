-- Prove2me | Theorems.Thm_GlobalTheory_IsAlgebraicIn_comp
-- name    : GlobalTheory.IsAlgebraicIn.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:52.90846+00:00
-- url     : https://prove2.me/theorems/d4fc6bf2-f780-4ed8-a8f2-c910b25097b7
-- title:
--   Is Algebraic In: comp
-- statement:
--   The Is Algebraic In construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L153-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L153-L156

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
variable {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V']
omit [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

theorem GlobalTheory.IsAlgebraicIn.comp {L : RigLB G} {y : Sp ℂ ⟶ S} {e : V → (Sp ℂ ⟶ G.left)} {θ : V → ℂ}
    {fr : L.L.ι → V → ℂ} (H : IsAlgebraicIn L y e θ fr) (h : V' → V) :
    IsAlgebraicIn L y (fun z => e (h z)) (fun z => θ (h z)) (fun j z => fr j (h z)) := by sorry
