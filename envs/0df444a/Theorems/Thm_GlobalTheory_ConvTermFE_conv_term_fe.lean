-- Prove2me | Theorems.Thm_GlobalTheory_ConvTermFE_conv_term_fe
-- name    : GlobalTheory.ConvTermFE.conv_term_fe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:14:54.801857+00:00
-- url     : https://prove2.me/theorems/fdf23368-f29b-4c06-a2fb-9c24c3f73b42
-- title:
--   Conv Term FE: conv term fe
-- statement:
--   The Conv Term FE construction uses the conv term fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ConvTermFe.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ConvTermFe.lean#L56-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TranslationUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.ConvTermFE.conv_term_fe : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k l : ℕ) (s : Raw D F k) (s' : Raw D F l), DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ∀ (mu α β ga β' ga' : D.X), β + ga = α → β' = β + k • mu → ga' = ga + l • mu → ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α) → ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J), Good D.P.L z J → sval (s β') r.left z J * sval (s' ga') r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β') (toUnit Z ≫ D.c ga') (r ≫ snd _ _)).val = sval (s β) (r ≫ DegPre.trF D F mu).left z J * sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) ((r ≫ DegPre.trF D F mu) ≫ snd _ _)).val * (val u r.left z J).val := by sorry
