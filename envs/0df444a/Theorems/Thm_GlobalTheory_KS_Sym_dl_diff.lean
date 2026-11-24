-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_dl_diff
-- name    : GlobalTheory.KS.Sym.dl_diff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:43.337695+00:00
-- url     : https://prove2.me/theorems/b06ba75c-ed16-4fc5-b9e9-963aebf666a5
-- title:
--   Sym: dl diff
-- statement:
--   The Sym construction uses the dl diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L419-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L419-L456

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

theorem GlobalTheory.KS.Sym.dl_diff {g : ℕ} {m : Y ⟶ X} {D : R → K}
    {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} {Q Q' Q₀ : X₂.Opens}
    {d₂ d₂' : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)} (hd₂ : LocDerK q₂ s₂ m₂ D Q d₂)
    (hd₂' : LocDerK q₂ s₂ m₂ D Q' d₂') {π : X₂ ⟶ X} {n p : Z ⟶ Y}
    (sq : m₂ ≫ π = n ≫ m) (l : Q₀ ≤ Q) (l' : Q₀ ≤ Q') {T : Y.Opens} (θ : Fin g → Γ(Y, T))
    (hT : m₂ ⁻¹ᵁ Q₀ ≤ p ⁻¹ᵁ T) {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    {w : Fin g → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hw : ∀ a, IsVF q₂ (w a))
    (hdiff : ∀ O, O ≤ Q₀ → ∀ f : Γ(X₂, O), d₂' O f - d₂ O f = ∑ a, pbT p (θ a) _ * w a _ (pbT m₂ f _))
    (ε : ℕ) (w₁ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ n ⁻¹ᵁ V → w a O (pbT n h O) = ε * pbT n (dd a V h) O)
    {L : LB X} {φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)} (hφ : IsDlog m L dd φ) (i j : L.ι) {O : Z.Opens}
    (hO : O ≤ m₂ ⁻¹ᵁ Q₀) (hi : O ≤ n ⁻¹ᵁ m ⁻¹ᵁ L.U i) (hj : O ≤ n ⁻¹ᵁ m ⁻¹ᵁ L.U j) :
    dl (n ≫ m) L (tr (𝟙 Z) m₂ π Q' d₂') i j O - dl (n ≫ m) L (tr (𝟙 Z) m₂ π Q d₂) i j O =
      ∑ a, pbT p (θ a) O * (ε * pbT n (φ a i j) O) := by sorry
