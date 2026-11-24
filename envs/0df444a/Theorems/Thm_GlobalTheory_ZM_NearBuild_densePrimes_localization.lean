-- Prove2me | Theorems.Thm_GlobalTheory_ZM_NearBuild_densePrimes_localization
-- name    : GlobalTheory.ZM.NearBuild.densePrimes_localization
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:42.722937+00:00
-- url     : https://prove2.me/theorems/56004690-49e0-4caa-bf9c-c0398c274fc9
-- title:
--   Near Build: dense Primes localization
-- statement:
--   The Near Build construction uses the dense Primes localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DenseOfDenseP.lean#L159-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DenseOfDenseP.lean#L159-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
variable {b Mat κ β v}

theorem GlobalTheory.ZM.NearBuild.densePrimes_localization (h : DenseP (objPrimes b Mat κ β v)) (f : R) :
    DenseP (objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a))) := by sorry
