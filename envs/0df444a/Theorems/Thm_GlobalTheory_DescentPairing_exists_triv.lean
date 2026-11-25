-- Prove2me | Theorems.Thm_GlobalTheory_DescentPairing_exists_triv
-- name    : GlobalTheory.DescentPairing.exists_triv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:23.729922+00:00
-- url     : https://prove2.me/theorems/1777b1bc-fed2-461a-9e77-f05e72ab907f
-- title:
--   Descent Pairing: exists triv
-- statement:
--   The Descent Pairing construction uses the exists triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenTranslEqPairing.lean#L106-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenTranslEqPairing.lean#L106-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DescentPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem GlobalTheory.DescentPairing.exists_triv {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (θ : ThetaGrp A L.L n T) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, val u (lift t a).left z J =
        cubN (cubV c z J) n 1 a (t ≫ θ.pt) * ((thetaVal θ t a z J)⁻¹ * s) := by sorry
