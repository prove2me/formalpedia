-- Prove2me | Theorems.Thm_GlobalTheory_LinDescent_exists_inv_sec_of_tame
-- name    : GlobalTheory.LinDescent.exists_inv_sec_of_tame
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:26.457731+00:00
-- url     : https://prove2.me/theorems/e29343e9-0ba0-4533-9297-9f60aaef6d0e
-- title:
--   Lin Descent: exists inv sec of tame
-- statement:
--   The Lin Descent construction uses the exists inv sec of tame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfInvGenOfInvariants.lean#L30-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfInvGenOfInvariants.lean#L30-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}

theorem GlobalTheory.LinDescent.exists_inv_sec_of_tame [Group C] [Finite C] (hL : L.IsLB)
    (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      (Nat.card {c // r ≫ t c = r} : k) ≠ 0)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X) c, r ≫ t c = r →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u c) r) (LB.oneGen L))
    {W : X.Opens} (hWa : IsAffineOpen W) (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) (x : X) (hx : x ∈ W) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∃ i, x ∈ X.basicOpen (s i) := by sorry
