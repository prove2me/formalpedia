-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobField_Good_sup
-- name    : GlobalTheory.SS.FrobField.Good.sup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:14.175984+00:00
-- url     : https://prove2.me/theorems/40652f41-34bd-40aa-9b57-720d4311cc6a
-- title:
--   Good: sup
-- statement:
--   The Good construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L123-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField

theorem GlobalTheory.SS.FrobField.Good.sup {X : Scheme.{0}} {F : End X} {q : ℕ} {U V W : X.Opens} (f : Γ(X, W))
    (hU : U ≤ W) (hV : V ≤ W) (hW : W = U ⊔ V)
    (a : Good F q U ((X.presheaf.map (homOfLE hU).op).hom f))
    (b : Good F q V ((X.presheaf.map (homOfLE hV).op).hom f)) : Good F q W f := by sorry
