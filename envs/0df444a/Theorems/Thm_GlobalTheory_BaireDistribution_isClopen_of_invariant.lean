-- Prove2me | Theorems.Thm_GlobalTheory_BaireDistribution_isClopen_of_invariant
-- name    : GlobalTheory.BaireDistribution.isClopen_of_invariant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:00.472615+00:00
-- url     : https://prove2.me/theorems/4cdad13d-2a50-44a8-83fb-6b8f47f153bf
-- title:
--   Baire Distribution: is Clopen of invariant
-- statement:
--   The Baire Distribution construction uses the is Clopen of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L74-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.BaireDistribution.isClopen_of_invariant {K : Subgroup G} (hK : IsOpen (K : Set G)) {C : Set G}
    (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ g, a * g * b ∈ C ↔ g ∈ C) : IsClopen C := by sorry
