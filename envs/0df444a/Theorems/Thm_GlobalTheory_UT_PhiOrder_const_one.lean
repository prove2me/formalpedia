-- Prove2me | Theorems.Thm_GlobalTheory_UT_PhiOrder_const_one
-- name    : GlobalTheory.UT.PhiOrder.const_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:20:14.235457+00:00
-- url     : https://prove2.me/theorems/5cb18847-acd1-42ab-bf3a-6c8650045dce
-- title:
--   Phi Order: const one
-- statement:
--   The Phi Order construction uses the const one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L296-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L296-L331

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UT.PhiOrder.const_one (hB : D.TauBimult) (hE : D.PsiEven) {k : ℕ} (hk : Odd k) (p : QkPt D F k) (w : Frm D F k p.g.b)
    (hw : TXFrame k p w) (z : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    (∏ i ∈ Finset.range k, H1.hv (th D z J) k ((p.g.b ^ k) ^ i) p.g.b (p.g.b ^ (k - 1 - i)) *
        (val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J)) *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J)⁻¹ = 1 := by sorry
