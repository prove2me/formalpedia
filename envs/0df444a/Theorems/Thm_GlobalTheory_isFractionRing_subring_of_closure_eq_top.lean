-- Prove2me | Theorems.Thm_GlobalTheory_isFractionRing_subring_of_closure_eq_top
-- name    : GlobalTheory.isFractionRing_subring_of_closure_eq_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:27.64024+00:00
-- url     : https://prove2.me/theorems/7edd254c-1605-4185-b7b8-648f3799a7af
-- title:
--   Global Theory: is Fraction Ring subring of closure eq top
-- statement:
--   The Global Theory construction uses the is Fraction Ring subring of closure eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsFractionRingSubringOfClosureEqTop.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsFractionRingSubringOfClosureEqTop.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsFractionRingSubringOfClosureEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.isFractionRing_subring_of_closure_eq_top {Ω : Type*} [Field Ω] {t : Set Ω}
    (ht : Subfield.closure t = ⊤) (D : Subring Ω) (hD : t ⊆ D) : IsFractionRing D Ω := by sorry
