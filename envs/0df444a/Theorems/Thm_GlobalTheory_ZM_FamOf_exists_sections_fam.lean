-- Prove2me | Theorems.Thm_GlobalTheory_ZM_FamOf_exists_sections_fam
-- name    : GlobalTheory.ZM.FamOf.exists_sections_fam
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:30.944139+00:00
-- url     : https://prove2.me/theorems/0db9f60a-a32c-512e-9744-7d9386b0ab98
-- title:
--   Fam Of: exists sections fam
-- statement:
--   The Fam Of construction uses the exists sections fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSectionsFam.lean#L118-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSectionsFam.lean#L118-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSectionsFam
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FamOf

theorem GlobalTheory.ZM.FamOf.exists_sections_fam : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) (Hh : Type) (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ) (d : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec), DenseP (objPrimes b Mat κ β v) → FibData b Mat κ β v m p hh Q d → (∀ h, Ideal.span (Set.range (p h)) = ⊤) → ProjRep (vanIdeal d (fun h i => p (hh h) i)) Z.hom M th → Flat Z.hom → (∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : Ix g (N' ^ 2) → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (p (hh h) i)) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : Ix g (N' ^ 2) → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w) → ∃ sc, Fam b Mat κ β v m M th sc := by sorry
