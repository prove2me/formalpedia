-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_eq_kerSet
-- name    : GlobalTheory.HeckeCompare.eq_kerSet
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:27.386814+00:00
-- url     : https://prove2.me/theorems/3352e527-a3b7-46c4-84ea-95d20a38ceb9
-- title:
--   Hecke Compare: eq ker Set
-- statement:
--   The Hecke Compare construction uses the eq ker Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L462-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L462-L491

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
variable (I : TateIso D k Q (fun a x => ρ a x) e) (hu : Uniq e) (hρ : IsAct ρ) {P : Ideal (𝓞 E)} [hP : P.IsMaximal]
  (hco : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {p : ℕ} (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
include I hu hρ hco
include hp hpP
variable {C₀ : Subgroup Q} (h₁ : ∀ a, ∀ x ∈ C₀, ρ a x ∈ C₀)
  (h₂ : ∀ x ∈ C₀, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
include h₂
include h₁
omit h₁ h₂

theorem GlobalTheory.HeckeCompare.eq_kerSet [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) (C : Subgroup Q)
    (c₁ : ∀ x ∈ C, ∀ a, ρ a x ∈ C)
    (c₃ : ∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
    (c₄ : ∀ x ∈ C, ∀ y ∈ C, e (p * p) x y 1) (c₅ : Nat.card C = Nat.card {x : Q // x ^ p = 1}) :
    (∀ a, ∀ x ∈ C.map (powMonoidHom p), ρ a x ∈ C.map (powMonoidHom p)) ∧
    (∀ x ∈ C.map (powMonoidHom p), ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1) ∧
    (C : Set Q) = kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) (C.map (powMonoidHom p)) := by sorry
