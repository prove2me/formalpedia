-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SectionsThroughEpsilonPoints_fracMap_algebraMap
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:16:04.21992+00:00
-- url     : https://prove2.me/theorems/4ad8280e-2705-45a9-a871-2846e3a8a73f
-- title:
--   Sections Through Epsilon Points: frac Map algebra Map
-- statement:
--   The Sections Through Epsilon Points construction uses the frac Map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/ArcFramePointTruncation.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/ArcFramePointTruncation.lean#L92-L93

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_ArcFramePointTruncation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (dualMap FrPt Gx PPx IsCombAt embK)
open scoped CategoryTheory.Obj
variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {g : A →+* A'}
  {D₀ : Out.DegPre A} {D₁ : Out.DegPre A'}

theorem GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap (hg : Function.Injective g) (r : A) :
    fracMap g hg (algebraMap A _ r) = algebraMap A' _ (g r) := by sorry
