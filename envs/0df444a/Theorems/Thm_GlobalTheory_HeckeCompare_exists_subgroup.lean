-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_exists_subgroup
-- name    : GlobalTheory.HeckeCompare.exists_subgroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:18.759452+00:00
-- url     : https://prove2.me/theorems/76cbf4ab-81a3-48b2-b4d6-58bf6e714c89
-- title:
--   Hecke Compare: exists subgroup
-- statement:
--   The Hecke Compare construction uses the exists subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L319-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L319-L412

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

theorem GlobalTheory.HeckeCompare.exists_subgroup [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) :
    ∃ C : Subgroup Q, (C : Set Q) = kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ ∧
      (∀ x ∈ C, ∀ a, ρ a x ∈ C) ∧
      (∀ J : Ideal (𝓞 E), J * P = Ideal.span {(p : 𝓞 E)} → ∀ x, (∀ a ∈ J, ρ a x = 1) → x ∈ C) ∧
      (∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1) ∧
      (∀ x ∈ C, ∀ y ∈ C, e (p * p) x y 1) ∧ Nat.card C = Nat.card {x : Q // x ^ p = 1} ∧
      Nat.card {x : Q // x ^ p = 1} = Nat.card {x : Q // x ∈ C ∧ x ^ p = 1} * Nat.card C₀ := by sorry
