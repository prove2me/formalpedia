-- Prove2me | Theorems.Thm_GlobalTheory_adjCompare
-- name    : GlobalTheory.adjCompare
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:52:15.232674+00:00
-- url     : https://prove2.me/theorems/8c845329-f725-4d28-9d58-15e4a1aa2546
-- title:
--   Global Theory: adj Compare
-- statement:
--   The Global Theory construction uses the adj Compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L122-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L122-L163

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GrpPullbackSquareProductLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {σ : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G σ φ)

theorem GlobalTheory.adjCompare (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') {P : LB (G ⊗ G).left} (hP : P.IsLB)
    {K L : Type} [Fintype K] [Fintype L] {τ : K → ((G' ⊗ G').left ⟶ (G ⊗ G).left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb P τ ε)) (ht : t.IsGen) {ω : L → ((G3 G).left ⟶ (G ⊗ G).left)} {δ : L → ℤ}
    (w : LB.Gen (LB.LinComb P ω δ)) (hw : w.IsGen) (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 G' ⟶ G')
    (hF : ∀ (U : Type) [CommGroup U] (h : ((G3 G').left ⟶ (G ⊗ G).left) → U),
      (∏ i, h (adjPair3 gp l₁ l₂ l₃ ≫ ω i) ^ δ i) * ((∏ i, h ((lift a₁ b₁).left ≫ τ i) ^ ε i) *
        (∏ i, h ((lift a₂ b₂).left ≫ τ i) ^ ε i)) =
      (∏ i, h (adjPair3 gp k₁ k₂ k₃ ≫ ω i) ^ δ i) * ((∏ i, h ((lift a b).left ≫ τ i) ^ ε i) *
        (∏ i, h ((lift (1 : G3 G' ⟶ G') (1 : G3 G' ⟶ G')).left ≫ τ i) ^ ε i)))
    (h0 : ∀ q ∈ [a, b, a₁, b₁, a₂, b₂, k₁, k₂, k₃, l₁, l₂, l₃],
      (lift 1 (lift 1 1) : 𝟙_ (Over S') ⟶ G3 G') ≫ q = 1)
    {T : Over S'} (ρ : T ⟶ G3 G') {z : T.left} {J} (hJ : Good P z J) :
    val w (adjPair3 gp (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃)) z J * (val t (lift (ρ ≫ a) (ρ ≫ b)).left z J *
      val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
    val w (adjPair3 gp (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃)) z J * (val t (lift (ρ ≫ a₁) (ρ ≫ b₁)).left z J *
      val t (lift (ρ ≫ a₂) (ρ ≫ b₂)).left z J) := by sorry
