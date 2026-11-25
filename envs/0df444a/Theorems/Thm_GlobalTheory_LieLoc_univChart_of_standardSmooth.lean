-- Prove2me | Theorems.Thm_GlobalTheory_LieLoc_univChart_of_standardSmooth
-- name    : GlobalTheory.LieLoc.univChart_of_standardSmooth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:39:10.86023+00:00
-- url     : https://prove2.me/theorems/c7981f16-b25c-4565-b867-6894d837fe82
-- title:
--   Lie Loc: univ Chart of standard Smooth
-- statement:
--   The Lie Loc construction uses the univ Chart of standard Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/UnivChartOfStandardSmooth.lean#L26-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/UnivChartOfStandardSmooth.lean#L26-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]

theorem GlobalTheory.LieLoc.univChart_of_standardSmooth (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) (ε : S →ₐ[R] R) (hε : spMap ε ≫ j = 1)
    (hj : ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), IsNilpotent (RingHom.ker aug) →
      ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ φ : S →ₐ[R] A, y = spMap φ ≫ j)
    (hinj : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : S →ₐ[R] A),
      spMap φ ≫ j = spMap φ' ≫ j → φ = φ') :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G, IsUnivChart G n x := by sorry
