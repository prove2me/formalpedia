-- Prove2me | Theorems.Thm_GlobalTheory_UU_TwistNonvan_sum_eq_zero
-- name    : GlobalTheory.UU.TwistNonvan.sum_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:45:08.90864+00:00
-- url     : https://prove2.me/theorems/fd6804a3-920e-5eb7-82ba-5cdb9ae24bfc
-- title:
--   Twist Nonvan: sum eq zero
-- statement:
--   The Twist Nonvan construction uses the sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistConvNeZero.lean#L41-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistConvNeZero.lean#L41-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffEqZeroOfSumSmulEqZeroOfSeparating
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteExtensionPrimitiveResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfFaithfullyFlatBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsNeZeroIffSvalGenericPointNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistConvNeZero
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.TwistNonvan

theorem GlobalTheory.UU.TwistNonvan.sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by sorry
