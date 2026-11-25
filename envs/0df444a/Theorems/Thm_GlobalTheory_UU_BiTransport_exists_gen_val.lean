-- Prove2me | Theorems.Thm_GlobalTheory_UU_BiTransport_exists_gen_val
-- name    : GlobalTheory.UU.BiTransport.exists_gen_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:43:25.808782+00:00
-- url     : https://prove2.me/theorems/5f1a5305-fb40-4084-969b-fc5ef6be686c
-- title:
--   Bi Transport: exists gen val
-- statement:
--   The Bi Transport construction uses the exists gen val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivTransport.lean#L66-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivTransport.lean#L66-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}

theorem GlobalTheory.UU.BiTransport.exists_gen_val [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsPullback E H₀.hom H.hom ρ)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F)
    (σ : LB.Gen (LB.LinComb P₀.L.L (lamφ i₀) Oε)) (hσ : σ.IsGen) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      ∀ (T : Over S₀) (t : T ⟶ H₀) (x : T ⟶ G₀) (a : T.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (toBase hE.w t) (toBase hw x)).left →
        ∀ (z : T.left) (J' J), Good P₀.L.L z J' → Good P.L.L z J →
        ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ y, W y = gw w y.left z (J (y.left ≫ F)) (J' y.left)) →
          val s a z J = W ((t ≫ i₀) * x) * (W (t ≫ i₀))⁻¹ * (W x)⁻¹ * W 1 * val σ (lift t x).left z J' := by sorry
