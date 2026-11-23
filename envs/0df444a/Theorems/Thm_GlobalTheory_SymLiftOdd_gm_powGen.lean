-- Prove2me | Theorems.Thm_GlobalTheory_SymLiftOdd_gm_powGen
-- name    : GlobalTheory.SymLiftOdd.gm_powGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:55.806822+00:00
-- url     : https://prove2.me/theorems/a0b10ac3-7b4d-4d6c-8b41-2442d41469bc
-- title:
--   Sym Lift Odd: gm pow Gen
-- statement:
--   The Sym Lift Odd construction uses the gm pow Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L147-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L147-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}

theorem GlobalTheory.SymLiftOdd.gm_powGen (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (j : Fin n × Fin 2 → L.ι) (hj : r z ∈ LB.wchart L (powφ A θ.pt n) j) :
    gm r z (LB.wchart L (powφ A θ.pt n) j) ((powGen A L k θ n).s j) =
      ∏ j₀ : Fin n, gm r z (LB.wchart L (fun b => (translT A (θ.pt ^ (j₀ : ℕ))).left ≫
            (![(snd T A).left, (translPt A θ.pt).left] b)) (fun b => j (j₀, b)))
        ((LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
          (translT A (θ.pt ^ (j₀ : ℕ))).left).s (fun b => j (j₀, b))) := by sorry
