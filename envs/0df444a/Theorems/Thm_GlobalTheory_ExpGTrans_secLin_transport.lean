-- Prove2me | Theorems.Thm_GlobalTheory_ExpGTrans_secLin_transport
-- name    : GlobalTheory.ExpGTrans.secLin_transport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:49.362035+00:00
-- url     : https://prove2.me/theorems/5882dcbe-7d01-46b9-b310-e693cd03f4f1
-- title:
--   Exp GTrans: sec Lin transport
-- statement:
--   The Exp GTrans construction uses the sec Lin transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L58-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L58-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
variable {X X' Y Y' Y₁ Y₁' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K' : Type} [Fintype K] [Fintype K']

theorem GlobalTheory.ExpGTrans.secLin_transport (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    (φ₁ : K → (Y₁ ⟶ X)) (φ₁' : K → (Y₁' ⟶ X')) (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ)
    (h : Y₁ ⟶ Y) (h' : Y₁' ⟶ Y') (Θ : Y₁' ⟶ Y₁) (Φ : Y' ⟶ Y)
    (hφ : ∀ κ, φ₁ κ = h ≫ φ κ) (hφ' : ∀ κ, φ₁' κ = h' ≫ φ' κ) (hc : ∀ κ, φ' κ ≫ F = Φ ≫ φ κ)
    (hsq : Θ ≫ h = h' ≫ Φ) {n : ℕ} (c : Fin n → Γ(Y₁, ⊤)) (c' : Fin n → Γ(Y₁', ⊤))
    (hcc : ∀ i y, gs (𝟙 Y₁' ≫ Θ) y ⊤ (c i) = gs (𝟙 Y₁') y ⊤ (c' i))
    (s₁ : LB.Sec (LB.LinComb L φ₁ ε)) (s₁' : LB.Sec (LB.LinComb L' φ₁' ε))
    (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (s' : Fin n → LB.Sec (LB.LinComb L' φ' ε))
    (H₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ₁' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ₁' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart L φ₁ p) (s₁.f p) =
        (∏ κ, gw w (r ≫ φ₁' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ₁' q) (s₁'.f q))
    (H : ∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ Φ) z (LB.wchart L φ p) ((s i).f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) ((s' i).f q))
    (hS : GeneratorPullback.SecLin L φ₁ ε s₁ φ ε s h c) : GeneratorPullback.SecLin L' φ₁' ε s₁' φ' ε s' h' c' := by sorry
