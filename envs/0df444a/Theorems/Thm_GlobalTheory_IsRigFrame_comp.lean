-- Prove2me | Theorems.Thm_GlobalTheory_IsRigFrame_comp
-- name    : GlobalTheory.IsRigFrame.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:51.929869+00:00
-- url     : https://prove2.me/theorems/e03d77a2-8635-42b2-8a6a-e4ff510f21e1
-- title:
--   Is Rig Frame: comp
-- statement:
--   The Is Rig Frame construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L144-L149

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

theorem GlobalTheory.IsRigFrame.comp {L : RigLB G} {y : Sp ℂ ⟶ S} {e : V → (Sp ℂ ⟶ G.left)} {fr : L.L.ι → V → ℂ}
    (H : IsRigFrame L y e fr) (h : V' →L[ℂ] V) : IsRigFrame L y (fun z => e (h z)) (fun j z => fr j (h z)) := by sorry
