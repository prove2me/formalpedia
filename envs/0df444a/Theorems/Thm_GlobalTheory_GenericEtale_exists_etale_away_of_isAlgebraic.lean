-- Prove2me | Theorems.Thm_GlobalTheory_GenericEtale_exists_etale_away_of_isAlgebraic
-- name    : GlobalTheory.GenericEtale.exists_etale_away_of_isAlgebraic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:03.657464+00:00
-- url     : https://prove2.me/theorems/f543e15d-d939-4e5f-8206-40ff7ccf7188
-- title:
--   Generic Etale: exists etale away of is Algebraic
-- statement:
--   The Generic Etale construction uses the exists etale away of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleAwayOfIsAlgebraic.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleAwayOfIsAlgebraic.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleAwayOfIsAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.GenericEtale

theorem GlobalTheory.GenericEtale.exists_etale_away_of_isAlgebraic : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Algebra.Etale A' B' := by sorry
