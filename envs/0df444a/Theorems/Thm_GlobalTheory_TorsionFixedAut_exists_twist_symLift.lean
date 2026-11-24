-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_exists_twist_symLift
-- name    : GlobalTheory.TorsionFixedAut.exists_twist_symLift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:50.519794+00:00
-- url     : https://prove2.me/theorems/611ce599-f5f0-4729-80ee-516022d8070a
-- title:
--   Torsion Fixed Aut: exists twist sym Lift
-- statement:
--   The Torsion Fixed Aut construction uses the exists twist sym Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L323-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L323-L387

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
variable (σ : A ⟶ A) (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))
variable [IsMonHom σ]

theorem GlobalTheory.TorsionFixedAut.exists_twist_symLift [IsCommMonObj A] (hL : L.IsLB) (hc : c.IsGen) {k : ℤ} {n : ℕ} (θ : ThetaGrp A L k T)
    (hn : θ.pt ^ n = 1) (hx : θ.pt ≫ σ = θ.pt) (hθ : SymLift A L k n θ.pt θ) :
    ∃ (t : LB.Gen (thetaLB A L k θ.pt)) (ht : t.IsGen), SymLift A L k n θ.pt ⟨θ.pt, t, ht⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        thetaVal t r z J =
        thetaVal θ.φ (r ≫ (T ◁ σ).left) z J *
          (val c (r ≫ (snd T A).left) z J ^ k * val c (r ≫ (translPt A θ.pt).left) z J ^ (-k))⁻¹ := by sorry
