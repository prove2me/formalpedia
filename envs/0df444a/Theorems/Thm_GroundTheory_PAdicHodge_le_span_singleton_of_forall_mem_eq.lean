-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_le_span_singleton_of_forall_mem_eq
-- name    : GroundTheory.PAdicHodge.le_span_singleton_of_forall_mem_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:25.131804+00:00
-- url     : https://prove2.me/theorems/f1234974-0786-428b-be6b-dfab4c085e81
-- title:
--   PAdic Hodge: le span singleton of forall mem eq
-- statement:
--   The PAdic Hodge construction uses the le span singleton of forall mem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {R : Type*} [CommRing R]

theorem GroundTheory.PAdicHodge.le_span_singleton_of_forall_mem_eq {π ξ : R} [IsAdicComplete (Ideal.span {π}) R]
    {J : Ideal R} (h : ∀ x ∈ J, ∃ a z, z ∈ J ∧ x = a * ξ + z * π) :
    J ≤ Ideal.span {ξ} := by sorry
