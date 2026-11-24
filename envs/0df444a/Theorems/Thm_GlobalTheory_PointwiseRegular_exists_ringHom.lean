-- Prove2me | Theorems.Thm_GlobalTheory_PointwiseRegular_exists_ringHom
-- name    : GlobalTheory.PointwiseRegular.exists_ringHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:54.791425+00:00
-- url     : https://prove2.me/theorems/110d14c8-5362-42a4-b572-3b5010edb564
-- title:
--   Pointwise Regular: exists ring Hom
-- statement:
--   The Pointwise Regular construction uses the exists ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniqueHomOfLocallyRegular.lean#L65-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniqueHomOfLocallyRegular.lean#L65-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.PointwiseRegular

theorem GlobalTheory.PointwiseRegular.exists_ringHom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : Y.left.Opens) (D : X.left.Opens)
    (hF : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ (F y).left ⁻¹ᵁ D)
    (h : ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U ρ = valAt' (F y).left D φ) :
    ∃ r : Γ(X.left, D) →+* Γ(Y.left, U), ∀ φ, ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U (r φ) = valAt' (F y).left D φ := by sorry
