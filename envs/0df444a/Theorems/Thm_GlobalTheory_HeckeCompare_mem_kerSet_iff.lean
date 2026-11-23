-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_mem_kerSet_iff
-- name    : GlobalTheory.HeckeCompare.mem_kerSet_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:36.985696+00:00
-- url     : https://prove2.me/theorems/3677df90-b35b-4278-ae6a-143aac6ee6a2
-- title:
--   Hecke Compare: mem ker Set iff
-- statement:
--   The Hecke Compare construction uses the mem ker Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L281-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L281-L307

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

theorem GlobalTheory.HeckeCompare.mem_kerSet_iff (x : Q) : x ∈ kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ ↔
    ∃ x' x₂ : Q, x = x' * x₂ ∧ (x' ^ p = 1 ∧ ∀ c ∈ C₀, e p x' c 1) ∧
      (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀ := by sorry
