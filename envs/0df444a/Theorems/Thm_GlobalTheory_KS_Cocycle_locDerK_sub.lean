-- Prove2me | Theorems.Thm_GlobalTheory_KS_Cocycle_locDerK_sub
-- name    : GlobalTheory.KS.Cocycle.locDerK_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:56.699527+00:00
-- url     : https://prove2.me/theorems/adb5c652-aa4a-439a-84ef-badbf8ca38d0
-- title:
--   Cocycle: loc Der K sub
-- statement:
--   The Cocycle construction uses the loc Der K sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnZero.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnZero.lean#L45-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationLiftSmoothOverFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnZero
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Cocycle

theorem GlobalTheory.KS.Cocycle.locDerK_sub {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D : R → K} {W₁ W₂ W₀ : X.Opens} {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂) (l₁ : W₀ ≤ W₁) (l₂ : W₀ ≤ W₂) :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d₂ W f - d₁ W f) := by sorry
