-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBundleSym_exists_sec
-- name    : GlobalTheory.ThetaBundleSym.exists_sec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:43.364684+00:00
-- url     : https://prove2.me/theorems/9cc0a2d9-20cd-41b0-b49c-d5b6c128532d
-- title:
--   Theta Bundle Sym: exists sec
-- statement:
--   The Theta Bundle Sym construction uses the exists sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfComplexPoints.lean#L46-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfComplexPoints.lean#L46-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
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
open GlobalTheory GlobalTheory.ThetaBundleSym
variable {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {Z : Type} {ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)}

theorem GlobalTheory.ThetaBundleSym.exists_sec (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
      valAt' x.left U f = valAt' x.left U f') → f = f')
    (M : LB X.left) (v : M.ι → Z → ℂ)
    (hv : ∀ i, ∃ (W : X.left.Opens) (φ : Γ(X.left, W)), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i →
      ⊤ ≤ (ex z).left ⁻¹ᵁ W ∧ valAt' (ex z).left W φ = v i z)
    (hc : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (ex z).left ⁻¹ᵁ M.U j →
      v i z = valAt' (ex z).left (M.U i ⊓ M.U j) (M.g i j).val * v j z) :
    ∃ s : M.Sec, ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → valAt' (ex z).left (M.U i) (s.f i) = v i z := by sorry
