-- Prove2me | Theorems.Thm_GlobalTheory_UU_IntGen_multK_frac
-- name    : GlobalTheory.UU.IntGen.multK_frac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:20.698214+00:00
-- url     : https://prove2.me/theorems/7790fba6-285a-505d-9050-70490b182829
-- title:
--   Int Gen: mult K frac
-- statement:
--   The Int Gen construction uses the mult K frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean#L125-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean#L125-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Theorems.Thm_GlobalTheory_UU_IsWt_inv

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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.IntGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.UU.IntGen.multK_frac (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D (𝟙_ _) α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ r₁ r₂ : R, r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (Z : Scheme.{0}) (σ : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J →
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₂) * (val (multK D k mu α) σ z J).val =
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₁) *
        (val v (σ ≫ (toUnit (TK R)).left) z J).val := by sorry
