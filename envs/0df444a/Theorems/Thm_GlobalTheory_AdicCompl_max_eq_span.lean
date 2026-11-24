-- Prove2me | Theorems.Thm_GlobalTheory_AdicCompl_max_eq_span
-- name    : GlobalTheory.AdicCompl.max_eq_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:55:47.260803+00:00
-- url     : https://prove2.me/theorems/e2cd6fc8-e946-4855-b4a0-b935cf609587
-- title:
--   Adic Compl: max eq span
-- statement:
--   The Adic Compl construction uses the max eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NumberFieldFinitePlaceCompletionEmbedding.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NumberFieldFinitePlaceCompletionEmbedding.lean#L47-L51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology
open GlobalTheory.AdicCompl
variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)
local notation "Lw" => adicCompletion L w
local notation "Ow" => adicCompletionIntegers L w

theorem GlobalTheory.AdicCompl.max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by sorry
