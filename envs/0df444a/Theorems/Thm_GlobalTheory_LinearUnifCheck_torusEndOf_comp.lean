-- Prove2me | Theorems.Thm_GlobalTheory_LinearUnifCheck_torusEndOf_comp
-- name    : GlobalTheory.LinearUnifCheck.torusEndOf_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:00.719835+00:00
-- url     : https://prove2.me/theorems/6b0b44c6-f5be-511a-876d-9f79593b980f
-- title:
--   Linear Unif Check: torus End Of comp
-- statement:
--   The Linear Unif Check construction uses the torus End Of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean#L33-L36

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

theorem GlobalTheory.LinearUnifCheck.torusEndOf_comp {h h' : X → X} {t t' : splitTorus S X ⟶ splitTorus S X}
    (ht : TorusEndOf X h t) (ht' : TorusEndOf X h' t') : TorusEndOf X (h ∘ h') (t ≫ t') := by sorry
