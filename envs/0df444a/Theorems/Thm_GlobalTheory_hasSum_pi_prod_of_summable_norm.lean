-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_pi_prod_of_summable_norm
-- name    : GlobalTheory.hasSum_pi_prod_of_summable_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T06:03:28.862204+00:00
-- url     : https://prove2.me/theorems/6398c7cc-281e-5afb-9996-8edcd939bff8
-- title:
--   Global Theory: has Sum pi prod of summable norm
-- statement:
--   The Global Theory construction uses the has Sum pi prod of summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumTupleProdOfSummableNormComplex.lean#L10-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumTupleProdOfSummableNormComplex.lean#L10-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumTupleProdOfSummableNormComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
open Filter Topology

theorem GlobalTheory.hasSum_pi_prod_of_summable_norm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by sorry
