-- Prove2me | Theorems.Thm_GlobalTheory_RigidTriv_exists_normalised
-- name    : GlobalTheory.RigidTriv.exists_normalised
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:09.935016+00:00
-- url     : https://prove2.me/theorems/371310a0-b42f-45b2-b63e-33bdf1a7830b
-- title:
--   Rigid Triv: exists normalised
-- statement:
--   The Rigid Triv construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean#L178-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean#L178-L212

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.RigidTriv.exists_normalised {N : LB Y} (hN : N.IsLB) {p : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ p = 𝟙 X)
    {r : (N.pull e).Gen} (hr : r.IsGen) (V : X.Opens) {s : ∀ i, Γ(Y, p ⁻¹ᵁ V ⊓ N.U i)ˣ}
    (hs : LocGen N (p ⁻¹ᵁ V) s) :
    ∃ s', LocGen N (p ⁻¹ᵁ V) s' ∧ ∀ x ∈ V, ∀ i, e x ∈ N.U i →
      gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s' i) = gm (𝟙 X) x ((N.pull e).U (fun _ => i)) (r.s fun _ => i) := by sorry
