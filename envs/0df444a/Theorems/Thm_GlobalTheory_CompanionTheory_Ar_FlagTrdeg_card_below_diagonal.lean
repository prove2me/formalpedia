-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagTrdeg_card_below_diagonal
-- name    : GlobalTheory.CompanionTheory.Ar.FlagTrdeg.card_below_diagonal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:17:37.079414+00:00
-- url     : https://prove2.me/theorems/95d06bf0-ec95-4ab5-ab5e-12ae168f3d17
-- title:
--   Flag Trdeg: card below diagonal
-- statement:
--   The Flag Trdeg construction uses the card below diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GenericFlagTrdegFormula.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GenericFlagTrdegFormula.lean#L10-L22

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_GenericFlagTrdegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagTrdeg
open scoped IntermediateField.algebraAdjoinAdjoin

theorem GlobalTheory.CompanionTheory.Ar.FlagTrdeg.card_below_diagonal (n : ℕ) :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n * (n - 1) / 2 := by sorry
