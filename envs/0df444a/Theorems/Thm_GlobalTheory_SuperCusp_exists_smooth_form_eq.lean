-- Prove2me | Theorems.Thm_GlobalTheory_SuperCusp_exists_smooth_form_eq
-- name    : GlobalTheory.SuperCusp.exists_smooth_form_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:50.333088+00:00
-- url     : https://prove2.me/theorems/c2138249-9154-48d3-b38a-961f108cc986
-- title:
--   Super Cusp: exists smooth form eq
-- statement:
--   The Super Cusp construction uses the exists smooth form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L52-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L52-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp

theorem GlobalTheory.SuperCusp.exists_smooth_form_eq {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {K N : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (a : G) (C : Set G)
    (hCK : ∀ c ∈ C, c ∈ K) (hfac : ∀ g ∈ K, ∃ x ∈ N, ∃ c ∈ C, g = x * c)
    (hcon : ∀ c ∈ C, a⁻¹ * c * a ∈ C) {u : V} (hu : ∀ g ∈ K, π g u = u) (l₀ : Module.Dual ℂ V)
    (hl : ∀ x ∈ N, ∀ v, l₀ (π x v) = l₀ v) :
    ∃ l ∈ smoothPart π.dual, ∀ r : ℕ, l (π (a ^ r) u) = l₀ (π (a ^ r) u) := by sorry
