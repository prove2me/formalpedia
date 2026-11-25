-- Prove2me | Theorems.Thm_GlobalTheory_ZM_NearBuild_fam_baseChange
-- name    : GlobalTheory.ZM.NearBuild.fam_baseChange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:23.545961+00:00
-- url     : https://prove2.me/theorems/b5f04da1-c295-44db-b22b-51b12ce9b655
-- title:
--   Near Build: fam base Change
-- statement:
--   The Near Build construction uses the fam base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ChartPullCompOfPullPull.lean#L37-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ChartPullCompOfPullPull.lean#L37-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ChartPullCompOfPullPull
import Theorems.Thm_GlobalTheory_ZM_NearBuild_FibData_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open GlobalTheory.ZM.NearBuild
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild

theorem GlobalTheory.ZM.NearBuild.fam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (R' : Type) [CommRing R'] (ρ : R →+* R') (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → Fam b Mat κ β v m M th sc → ∃ (th' : Ix g (N' ^ 2) → (M.pull π).Sec) (sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')), Fam b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (M.pull π) th' sc' ∧ ∀ (K : Type) [Field K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z'.left), Fib m (M.pull π) th' sc' x t φ → Fib m M th sc (x.comp ρ) t (φ ≫ π) := by sorry
