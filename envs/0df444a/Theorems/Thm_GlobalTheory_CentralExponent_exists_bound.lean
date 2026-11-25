-- Prove2me | Theorems.Thm_GlobalTheory_CentralExponent_exists_bound
-- name    : GlobalTheory.CentralExponent.exists_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:36.241814+00:00
-- url     : https://prove2.me/theorems/6dd0aeb8-efeb-414f-bf60-1461e170992f
-- title:
--   Central Exponent: exists bound
-- statement:
--   The Central Exponent construction uses the exists bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentralExponentBoundOver.lean#L18-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentralExponentBoundOver.lean#L18-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CentralExponent.exists_bound {π : Representation ℂ G V} (hπ : IsAdmissible π) (hU : IsUnitarisable π)
    {K N : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (a : G) (C : Set G)
    (hCK : ∀ c ∈ C, c ∈ K) (hfac : ∀ g ∈ K, ∃ x ∈ N, ∃ c ∈ C, g = x * c)
    (hcon : ∀ c ∈ C, a⁻¹ * c * a ∈ C) {u : V} (hu : ∀ g ∈ K, π g u = u) (l : V →ₗ[ℂ] ℂ)
    (hl : ∀ x ∈ N, ∀ v, l (π x v) = l v) : ∃ M : ℝ, ∀ r : ℕ, ‖l (π (a ^ r) u)‖ ≤ M := by sorry
