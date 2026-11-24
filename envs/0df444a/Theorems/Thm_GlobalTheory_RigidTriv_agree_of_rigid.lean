-- Prove2me | Theorems.Thm_GlobalTheory_RigidTriv_agree_of_rigid
-- name    : GlobalTheory.RigidTriv.agree_of_rigid
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:08.940531+00:00
-- url     : https://prove2.me/theorems/c1f75363-c15d-4311-8ecd-7314854ec60b
-- title:
--   Rigid Triv: agree of rigid
-- statement:
--   The Rigid Triv construction uses the agree of rigid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean#L214-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean#L214-L258

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

theorem GlobalTheory.RigidTriv.agree_of_rigid {N : LB Y} (hN : N.IsLB) {p : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ p = 𝟙 X)
    (rig : ∀ (V : X.Opens) (u : Γ(Y, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1)
    {V V' : X.Opens} {s : ∀ i, Γ(Y, p ⁻¹ᵁ V ⊓ N.U i)ˣ} {s' : ∀ i, Γ(Y, p ⁻¹ᵁ V' ⊓ N.U i)ˣ}
    (hs : LocGen N (p ⁻¹ᵁ V) s) (hs' : LocGen N (p ⁻¹ᵁ V') s')
    (h : ∀ x, x ∈ V → x ∈ V' → ∀ i, e x ∈ N.U i →
      gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s i) = gm e x (p ⁻¹ᵁ V' ⊓ N.U i) (s' i))
    (y : Y) (hy : p y ∈ V) (hy' : p y ∈ V') (i : N.ι) (hi : y ∈ N.U i) :
    gm (𝟙 Y) y (p ⁻¹ᵁ V ⊓ N.U i) (s i) = gm (𝟙 Y) y (p ⁻¹ᵁ V' ⊓ N.U i) (s' i) := by sorry
