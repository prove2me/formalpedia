-- Prove2me | Theorems.Thm_GlobalTheory_DegActCheck_psiUnitOn_iff_interior
-- name    : GlobalTheory.DegActCheck.psiUnitOn_iff_interior
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:32.086241+00:00
-- url     : https://prove2.me/theorems/8fc66b7a-3f6e-4f19-a3a5-4391fe6f916b
-- title:
--   Deg Act Check: psi Unit On iff interior
-- statement:
--   The Deg Act Check construction uses the psi Unit On iff interior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/PsiUnitOnIffInterior.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/PsiUnitOnIffInterior.lean#L11-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_PsiUnitOnIffInterior
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.DegActCheck.psiUnitOn_iff_interior (D : Out.DegPre R) (χ : D.X) (U : Set (Sp R)) :
    PsiUnitOn D χ U ↔ PsiUnitOn D χ (interior U) := by sorry
