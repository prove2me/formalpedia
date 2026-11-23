-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_nabs_properties
-- name    : GlobalTheory.SplitWeil.nabs_properties
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:27.282997+00:00
-- url     : https://prove2.me/theorems/2d5ee6b7-6829-4cdf-8cb7-9b8d6650208c
-- title:
--   Split Weil: nabs properties
-- statement:
--   The Split Weil construction uses the nabs properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitWeil.nabs_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k := by sorry
