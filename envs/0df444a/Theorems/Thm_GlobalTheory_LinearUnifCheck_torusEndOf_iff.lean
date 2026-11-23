-- Prove2me | Theorems.Thm_GlobalTheory_LinearUnifCheck_torusEndOf_iff
-- name    : GlobalTheory.LinearUnifCheck.torusEndOf_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:42.492546+00:00
-- url     : https://prove2.me/theorems/15b6248a-7a67-4a9c-8238-21c3ecf2c78d
-- title:
--   Linear Unif Check: torus End Of iff
-- statement:
--   The Linear Unif Check construction uses the torus End Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean#L17-L24

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

theorem GlobalTheory.LinearUnifCheck.torusEndOf_iff (h : X → X) (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by sorry
