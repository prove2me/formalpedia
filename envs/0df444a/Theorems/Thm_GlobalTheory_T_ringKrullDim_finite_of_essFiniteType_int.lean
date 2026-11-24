-- Prove2me | Theorems.Thm_GlobalTheory_T_ringKrullDim_finite_of_essFiniteType_int
-- name    : GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:56:33.767535+00:00
-- url     : https://prove2.me/theorems/acb4e502-c9a6-40bb-b5e2-d3ebb39a7c76
-- title:
--   T: ring Krull Dim finite of ess Finite Type int
-- statement:
--   The T construction uses the ring Krull Dim finite of ess Finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingKrullDimLtTopOfEssFiniteTypeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingKrullDimLtTopOfEssFiniteTypeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteTypeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int : ∀ (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D], ringKrullDim D < ⊤ := by sorry
