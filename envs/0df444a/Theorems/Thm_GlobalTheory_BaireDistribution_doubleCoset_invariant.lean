-- Prove2me | Theorems.Thm_GlobalTheory_BaireDistribution_doubleCoset_invariant
-- name    : GlobalTheory.BaireDistribution.doubleCoset_invariant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:59:58.182797+00:00
-- url     : https://prove2.me/theorems/a3e9adf2-0793-46fb-9de1-442c5ea4907b
-- title:
--   Baire Distribution: double Coset invariant
-- statement:
--   The Baire Distribution construction uses the double Coset invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L88-L98

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
omit [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.BaireDistribution.doubleCoset_invariant (K : Subgroup G) (x : G) : ∀ a ∈ K, ∀ b ∈ K, ∀ g,
    a * g * b ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} ↔
      g ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} := by sorry
