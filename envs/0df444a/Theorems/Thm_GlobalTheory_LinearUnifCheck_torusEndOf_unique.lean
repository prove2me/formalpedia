-- Prove2me | Theorems.Thm_GlobalTheory_LinearUnifCheck_torusEndOf_unique
-- name    : GlobalTheory.LinearUnifCheck.torusEndOf_unique
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:27.437487+00:00
-- url     : https://prove2.me/theorems/ab8f051c-f92f-4cf8-bd27-57aa66845692
-- title:
--   Linear Unif Check: torus End Of unique
-- statement:
--   The Linear Unif Check construction uses the torus End Of unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean#L26-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_NeTopOfAdmissibleBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LinearUnifCheck
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem GlobalTheory.LinearUnifCheck.torusEndOf_unique {h : X → X} {t t' : splitTorus S X ⟶ splitTorus S X}
    (ht : TorusEndOf X h t) (ht' : TorusEndOf X h t') : t = t' := by sorry
