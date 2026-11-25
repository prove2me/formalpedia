-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_genericFibre_of_affine_opens
-- name    : GlobalTheory.T.smooth_genericFibre_of_affine_opens
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:04.044884+00:00
-- url     : https://prove2.me/theorems/1458d6a7-a6b1-5e15-935a-212287dba415
-- title:
--   T: smooth generic Fibre of affine opens
-- statement:
--   The T construction uses the smooth generic Fibre of affine opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothGenericFibreOfAffineOpensStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothGenericFibreOfAffineOpensStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfAffineOpens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfAffineOpensStatement
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

theorem GlobalTheory.T.smooth_genericFibre_of_affine_opens : ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by sorry
