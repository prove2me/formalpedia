-- Prove2me | Theorems.Thm_GlobalTheory_ZV_ActsBy_comp
-- name    : GlobalTheory.ZV.ActsBy.comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:23.31871+00:00
-- url     : https://prove2.me/theorems/003e77dd-783e-4abd-9c62-d9e67881c600
-- title:
--   Acts By: comp
-- statement:
--   The Acts By construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean#L202-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean#L202-L217

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
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
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}

theorem GlobalTheory.ZV.ActsBy.comp [IsCommMonObj A] (hp : ∀ i, pt i ^ k = 1) {f g : A ⟶ A} [IsMonHom g]
    {F G : Matrix (Fin m) (Fin m) (ZMod k)} (hf : ActsBy pt f F) (hg : ActsBy pt g G) :
    ActsBy pt (f ≫ g) (G * F) := by sorry
