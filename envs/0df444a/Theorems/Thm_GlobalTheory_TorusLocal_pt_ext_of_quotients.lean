-- Prove2me | Theorems.Thm_GlobalTheory_TorusLocal_pt_ext_of_quotients
-- name    : GlobalTheory.TorusLocal.pt_ext_of_quotients
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:37.217587+00:00
-- url     : https://prove2.me/theorems/88280d8b-39ee-4074-9adf-868966a38641
-- title:
--   Torus Local: pt ext of quotients
-- statement:
--   The Torus Local construction uses the pt ext of quotients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialLocal.lean#L53-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialLocal.lean#L53-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
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
open GlobalTheory.TorusLocal
open TorusNil

theorem GlobalTheory.TorusLocal.pt_ext_of_quotients {A C : Type} [CommRing A] [CommRing C] [Algebra A C] {N : Type}
    (I : N → Ideal C) (hI : ∀ x, (∀ i, x ∈ I i) → x = 0)
    {B : Over (Spec (CommRingCat.of A))} [IsSeparated B.hom] {a b : sp A C ⟶ B}
    (h : ∀ i, spm (Ideal.Quotient.mkₐ A (I i)) ≫ a = spm (Ideal.Quotient.mkₐ A (I i)) ≫ b) :
    a = b := by sorry
