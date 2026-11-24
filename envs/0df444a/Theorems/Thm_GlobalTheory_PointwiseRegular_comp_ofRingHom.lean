-- Prove2me | Theorems.Thm_GlobalTheory_PointwiseRegular_comp_ofRingHom
-- name    : GlobalTheory.PointwiseRegular.comp_ofRingHom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:49.974448+00:00
-- url     : https://prove2.me/theorems/3934aff2-b91f-4208-b4ed-1cdd55d5e573
-- title:
--   Pointwise Regular: comp of Ring Hom
-- statement:
--   The Pointwise Regular construction uses the comp of Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniqueHomOfLocallyRegular.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniqueHomOfLocallyRegular.lean#L43-L63

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

theorem GlobalTheory.PointwiseRegular.comp_ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D)
    (r : Γ(X, D) →+* Γ(Y, U)) (y : Sp ℂ ⟶ U.toScheme) (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ D)
    (h : ∀ φ, valAt' (y ≫ U.ι) U (r φ) = valAt' x D φ) : y ≫ ofRingHom U hD r = x := by sorry
