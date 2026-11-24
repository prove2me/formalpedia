-- Prove2me | Theorems.Thm_GlobalTheory_BaireDistribution_isCompact_support
-- name    : GlobalTheory.BaireDistribution.isCompact_support
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:06.895801+00:00
-- url     : https://prove2.me/theorems/0b6a615d-5384-4cc4-8962-600e51a9f5eb
-- title:
--   Baire Distribution: is Compact support
-- statement:
--   The Baire Distribution construction uses the is Compact support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean#L26-L33

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
variable {X : Type} [TopologicalSpace X]

theorem GlobalTheory.BaireDistribution.isCompact_support (φ : SB X) : IsCompact (Function.support φ.1) := by sorry
