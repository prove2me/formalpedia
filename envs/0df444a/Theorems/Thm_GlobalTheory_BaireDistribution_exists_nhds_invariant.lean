-- Prove2me | Theorems.Thm_GlobalTheory_BaireDistribution_exists_nhds_invariant
-- name    : GlobalTheory.BaireDistribution.exists_nhds_invariant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:59:59.171709+00:00
-- url     : https://prove2.me/theorems/f7b74b7a-7aa9-471e-9ee9-0c6e03ce33e4
-- title:
--   Baire Distribution: exists nhds invariant
-- statement:
--   The Baire Distribution construction uses the exists nhds invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L100-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L100-L110

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

theorem GlobalTheory.BaireDistribution.exists_nhds_invariant (φ : SB G) :
    ∃ U ∈ nhds (1 : G), ∀ a ∈ U, ∀ b ∈ U, ∀ g, φ.1 (a * g * b) = φ.1 g := by sorry
