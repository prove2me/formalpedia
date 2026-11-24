-- Prove2me | Theorems.Thm_GlobalTheory_LieComb_lieComb_algebra
-- name    : GlobalTheory.LieComb.lieComb_algebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:23.762064+00:00
-- url     : https://prove2.me/theorems/2193e130-4e17-444a-b8a2-f0e96bfe291f
-- title:
--   Lie Comb: lie Comb algebra
-- statement:
--   The Lie Comb construction uses the lie Comb algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieBasisIffIsUnitDet.lean#L91-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieBasisIffIsUnitDet.lean#L91-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieComb
open GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem GlobalTheory.LieComb.lieComb_algebra (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (hv : ∀ i, IsTangent (v i)) :
    (∀ c, ∃! w, IsLieComb c v w) ∧ (∀ c w, IsLieComb c v w → IsTangent w) ∧
    (∀ (m : ℕ) (M : Fin m → Fin n → R) (v' : Fin m → (epsR R ⟶ G)) (c : Fin m → R) (w),
      (∀ i, IsLieComb (M i) v (v' i)) → IsLieComb c v' w → IsLieComb (∑ i, c i • M i) v w) ∧
    (∀ i, IsLieComb (Pi.single i 1) v (v i)) ∧
    ∀ (M : Matrix (Fin n) (Fin n) R) (v' : Fin n → (epsR R ⟶ G)), IsLieBasis v →
      (∀ i, IsLieComb (M i) v (v' i)) → (IsLieBasis v' ↔ IsUnit M.det) := by sorry
