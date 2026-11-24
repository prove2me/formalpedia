-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceIndex_congruence_finiteIndex
-- name    : GlobalTheory.CongruenceIndex.congruence_finiteIndex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:25.436532+00:00
-- url     : https://prove2.me/theorems/d44579c6-b20b-436e-9053-432b0ed1d366
-- title:
--   Congruence Index: congruence finite Index
-- statement:
--   The Congruence Index construction uses the congruence finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L189-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L189-L192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}

theorem GlobalTheory.CongruenceIndex.congruence_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → 0 < M → ∃ Γ : Subgroup (GL (Fin r) E), (∀ γ, γ ∈ Γ ↔ _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ := by sorry
