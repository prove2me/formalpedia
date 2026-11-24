-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_card_quot_span_algebraMap
-- name    : GlobalTheory.CNorm.card_quot_span_algebraMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:28.456076+00:00
-- url     : https://prove2.me/theorems/30fdf8ae-2f57-4429-9844-c27fc5a0124f
-- title:
--   CNorm: card quot span algebra Map
-- statement:
--   The CNorm construction uses the card quot span algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CardQuotSpanAlgebraMap.lean#L8-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CardQuotSpanAlgebraMap.lean#L8-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.card_quot_span_algebraMap : ∀ (R O : Type) [CommRing R] [Nontrivial R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O] (t : R), Nat.card (O ⧸ Ideal.span {algebraMap R O t}) = Nat.card (R ⧸ Ideal.span {t}) ^ Module.finrank R O := by sorry
