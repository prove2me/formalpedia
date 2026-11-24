-- Prove2me | Theorems.Thm_GlobalTheory_LevelCover_represents_pullback
-- name    : GlobalTheory.LevelCover.represents_pullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:57.27755+00:00
-- url     : https://prove2.me/theorems/baf885c4-cb7d-4aeb-beb1-ffad2a54f10f
-- title:
--   Level Cover: represents pullback
-- statement:
--   The Level Cover construction uses the represents pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean#L94-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean#L94-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l l₂ : Level H}

theorem GlobalTheory.LevelCover.represents_pullback (hC : ObjCompSt) (Xo : Moduli D l) {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B)
    (hR : ∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S →
      ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    {s : pullback Xo.s (spMap j) ⟶ Sp B} (hs : s = pullback.snd _ _) (o : Obj D l b s)
    (mo : ObjMap o Xo.univ (pullback.fst _ _)) : Represents o := by sorry
