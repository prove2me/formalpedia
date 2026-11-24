-- Prove2me | Theorems.Thm_GlobalTheory_PushInv_spread
-- name    : GlobalTheory.PushInv.spread
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:24.828276+00:00
-- url     : https://prove2.me/theorems/000019a1-b798-440c-9c9d-68b56af6859b
-- title:
--   Push Inv: spread
-- statement:
--   The Push Inv construction uses the spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L188-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L188-L227

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.PushInv.spread (π : Y ⟶ X) [GeometricallyIrreducible π] [IsReduced Y] (hπ : IsOpenMap π) {L : LB Y}
    {V W W' : X.Opens} {θ : ∀ i, Γ(Y, π ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (π ⁻¹ᵁ V))
    {s : ∀ i, Γ(Y, π ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (π ⁻¹ᵁ W)) (a : Γ(X, W')) (g : Y) (i : L.ι)
    (hV : π g ∈ V) (hW : π g ∈ W) (hW' : π g ∈ W') (hi : g ∈ L.U i)
    (e : gs (𝟙 Y) g _ (s i) = gs π g W' a * gs (𝟙 Y) g _ (θ i)) :
    ∃ O : X.Opens, π g ∈ O ∧ O ≤ W ∧ O ≤ W' ∧ ∀ k z, π z ∈ O → z ∈ L.U k →
      gs (𝟙 Y) z _ (s k) = gs π z W' a * gs (𝟙 Y) z _ (θ k) := by sorry
