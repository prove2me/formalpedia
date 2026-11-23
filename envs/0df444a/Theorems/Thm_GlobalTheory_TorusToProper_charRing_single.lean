-- Prove2me | Theorems.Thm_GlobalTheory_TorusToProper_charRing_single
-- name    : GlobalTheory.TorusToProper.charRing_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:27.468514+00:00
-- url     : https://prove2.me/theorems/1fa90ec4-d22f-48fc-8da6-4f1a2a83f664
-- title:
--   Torus To Proper: char Ring single
-- statement:
--   The Torus To Proper construction uses the char Ring single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L150-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
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
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
variable (K) (X : Type) [AddCommGroup X]

theorem GlobalTheory.TorusToProper.charRing_single (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) (a : X) :
    charRing X R φ (AddMonoidAlgebra.single a 1) = φ (Multiplicative.ofAdd a) := by sorry
