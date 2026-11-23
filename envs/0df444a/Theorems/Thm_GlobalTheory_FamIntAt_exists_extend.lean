-- Prove2me | Theorems.Thm_GlobalTheory_FamIntAt_exists_extend
-- name    : GlobalTheory.FamIntAt.exists_extend
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:00.520253+00:00
-- url     : https://prove2.me/theorems/c482a70e-d68b-44c6-bf5e-07b9a7239dce
-- title:
--   Fam Int At: exists extend
-- statement:
--   The Fam Int At construction uses the exists extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L24-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L24-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt

theorem GlobalTheory.FamIntAt.exists_extend {X Y Z : Scheme.{0}} [IsReduced Y] {L : LB X} (hL : L.IsLB) (ζ : Z ⟶ Y) (ξ : Z)
    (hξ : ∀ z : Z, z = ξ) (hd : ∀ U : Y.Opens, U ≠ ⊥ → ζ ξ ∈ U) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (t : LB.Sec (LB.LinComb L (fun k => ζ ≫ φ k) ε))
    (H : ∀ q : Y, ∃ (j : K → L.ι) (V : Y.Opens) (a : Γ(Y, V)), q ∈ V ∧ V ≤ LB.wchart L φ j ∧
      gs ζ ξ V a = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (T : Scheme.{0}) (r : T ⟶ Z) (z : T) (J), Good L z J →
      sval s (r ≫ ζ) z J = sval t r z J := by sorry
