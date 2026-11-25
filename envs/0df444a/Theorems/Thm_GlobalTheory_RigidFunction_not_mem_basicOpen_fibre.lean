-- Prove2me | Theorems.Thm_GlobalTheory_RigidFunction_not_mem_basicOpen_fibre
-- name    : GlobalTheory.RigidFunction.not_mem_basicOpen_fibre
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:50.032821+00:00
-- url     : https://prove2.me/theorems/50bade38-6270-4a57-862f-ca16caabbf2a
-- title:
--   Rigid Function: not mem basic Open fibre
-- statement:
--   The Rigid Function construction uses the not mem basic Open fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOneOfAppLESectionEqOne.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOneOfAppLESectionEqOne.lean#L16-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
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
open GlobalTheory
open GlobalTheory.RigidFunction

theorem GlobalTheory.RigidFunction.not_mem_basicOpen_fibre {X P F : Scheme.{0}} {K : Type} [Field K] {p : P ⟶ X}
    {t : Spec (CommRingCat.of K) ⟶ X} {φ : F ⟶ P} {q : F ⟶ Spec (CommRingCat.of K)} (w : φ ≫ p = q ≫ t)
    [IsIntegral F] [UniversallyClosed q] (V : X.Opens) (hV : ∀ x, t x ∈ V) (s : Γ(P, p ⁻¹ᵁ V)) (a b : F)
    (ha : φ a ∉ P.basicOpen s) : φ b ∉ P.basicOpen s := by sorry
