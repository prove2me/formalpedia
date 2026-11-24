-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzBruhat_distribution_eq_zero_baire
-- name    : GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:50.555146+00:00
-- url     : https://prove2.me/theorems/a23a3f60-7ba7-4d35-8af9-0c40e4895706
-- title:
--   T: schwartz Bruhat distribution eq zero baire
-- statement:
--   The T construction uses the schwartz Bruhat distribution eq zero baire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaireStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaireStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by sorry
