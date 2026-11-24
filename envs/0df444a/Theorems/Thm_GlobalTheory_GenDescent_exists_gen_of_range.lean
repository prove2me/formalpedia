-- Prove2me | Theorems.Thm_GlobalTheory_GenDescent_exists_gen_of_range
-- name    : GlobalTheory.GenDescent.exists_gen_of_range
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:23.09204+00:00
-- url     : https://prove2.me/theorems/34e47a50-821b-493d-8aca-da557b8afcd4
-- title:
--   Gen Descent: exists gen of range
-- statement:
--   The Gen Descent construction uses the exists gen of range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean#L127-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean#L127-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.GenDescent
variable {Y Y' Z : Scheme.{0}}

theorem GlobalTheory.GenDescent.exists_gen_of_range {N : LB Z} {f : Y ⟶ Z} {a} (ha : Compat N f a)
    (hinj : ∀ V, Function.Injective (f.app V).hom)
    (h₁ : ∀ i, (a i).val ∈ Set.range (f.app (N.U i)).hom)
    (h₂ : ∀ i, ((a i)⁻¹).val ∈ Set.range (f.app (N.U i)).hom) :
    ∃ t : N.Gen, t.IsGen := by sorry
