-- Prove2me | Theorems.Thm_GlobalTheory_LinDescent_exists_descent_of_invGen_of_invariants
-- name    : GlobalTheory.LinDescent.exists_descent_of_invGen_of_invariants
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:13.917283+00:00
-- url     : https://prove2.me/theorems/c6b44380-0edd-4331-8c03-76d407febffe
-- title:
--   Lin Descent: exists descent of inv Gen of invariants
-- statement:
--   The Lin Descent construction uses the exists descent of inv Gen of invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfInvGenOfInvariants.lean#L118-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfInvGenOfInvariants.lean#L118-L191

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

theorem GlobalTheory.LinDescent.exists_descent_of_invGen_of_invariants [Surjective π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : FunctionsAreInvariants t π) {u : ∀ c, LB.Gen (twist L (t c))}
    (V : Y → Y.Opens) (hV : ∀ y, y ∈ V y) (e : ∀ y i, Γ(X, π ⁻¹ᵁ V y ⊓ L.U i)ˣ)
    (he : ∀ y, IsInvGen u (π ⁻¹ᵁ V y) (e y)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by sorry
