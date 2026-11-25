-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_compat_of_affine
-- name    : GlobalTheory.KS.Sym.compat_of_affine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:23.616169+00:00
-- url     : https://prove2.me/theorems/ff1fa61c-be9b-4628-a38b-cb7a5439bf39
-- title:
--   Sym: compat of affine
-- statement:
--   The Sym construction uses the compat of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L287-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L287-L318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]

theorem GlobalTheory.KS.Sym.compat_of_affine {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W : X.Opens}
    {d : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (hW : IsAffineOpen W)
    {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} {Q : X₂.Opens}
    {d₂ : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)} (hd₂ : LocDerK q₂ s₂ m₂ D Q d₂) {π : X₂ ⟶ X} {p : Z ⟶ Y}
    (sq : m₂ ≫ π = p ≫ m) (hQ : Q ≤ π ⁻¹ᵁ W) (h0 : ∀ f : Γ(X, W), d₂ Q (pbT π f Q) = pbT p (d W f) _)
    {O : X.Opens} (hO : O ≤ W) (f : Γ(X, O)) {O₂ : X₂.Opens} (h₁ : O₂ ≤ Q) (h₂ : O₂ ≤ π ⁻¹ᵁ O) :
    d₂ O₂ (pbT π f O₂) = pbT p (d O f) _ := by sorry
