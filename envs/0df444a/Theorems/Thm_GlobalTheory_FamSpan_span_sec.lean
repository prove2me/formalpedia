-- Prove2me | Theorems.Thm_GlobalTheory_FamSpan_span_sec
-- name    : GlobalTheory.FamSpan.span_sec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:31.211439+00:00
-- url     : https://prove2.me/theorems/b5806fbe-c197-46f4-8e33-ef30af2c4cca
-- title:
--   Fam Span: span sec
-- statement:
--   The Fam Span construction uses the span sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIntegralFamiliesSpanPullDegeneration.lean#L119-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIntegralFamiliesSpanPullDegeneration.lean#L119-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem GlobalTheory.FamSpan.span_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ} (hc : ∀ κ, φ' κ ≫ F = F ≫ φ κ)
    (π : Y ⟶ X) (π' : Y' ⟶ X') (θ : Y ⟶ Y') (θ' : Y' ⟶ Y) (hθ : θ' ≫ θ = 𝟙 _) (hπ : θ ≫ π' ≫ F = π)
    {ψ' : K → (Y' ⟶ X')} (hψ : ∀ k, ψ' k = π' ≫ φ' k) {m : ℕ} (b g : Fin m → LB.Sec (LB.LinComb L φ ε))
    {C : Type} (κc : C → Γ(Y, ⊤))
    (hb : ∀ s : LB.Sec (LB.LinComb L (fun i => π ≫ φ i) ε), ∃ c : Fin m → C, ∀ j,
      s.f j = ∑ i, resTop (LB.wchart L (fun i => π ≫ φ i) j) (κc (c i)) *
        (show Γ(Y, LB.wchart L (fun i => π ≫ φ i) j) from (DVR.pullSec L φ ε (b i) π).f j))
    (ρ : Fin m → Γ(X, ⊤)) (hg : ∀ i j, (g i).f j = resTop _ (ρ i) * (b i).f j)
    (g' : Fin m → LB.Sec (LB.LinComb L' φ' ε))
    (hg' : ∀ i (y : Y') J J', Good L y J → Good L' y J' →
      sval (g i) ((𝟙 Y' ≫ π') ≫ F) y J = (fac w φ' ε (𝟙 Y' ≫ π') y J J').val * sval (g' i) (𝟙 Y' ≫ π') y J')
    (G : Fin m → LB.Sec (LB.LinComb L' ψ' ε)) (hG : ∀ i, GeneratorPullback.SecScal L' ψ' ε (G i) φ' ε (g' i) π' 1)
    (u : Fin m → Γ(Y', ⊤)) (hu : ∀ i, u i * (π' ≫ F).appTop.hom (ρ i) = 1)
    (s : LB.Sec (LB.LinComb L' ψ' ε)) :
    ∃ c : Fin m → C, ∀ j, s.f j = ∑ i, resTop (LB.wchart L' ψ' j) (θ'.appTop.hom (κc (c i)) * u i) *
      (show Γ(Y', LB.wchart L' ψ' j) from (G i).f j) := by sorry
