-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_mem_UJ_iff_adj_mul
-- name    : GlobalTheory.RegSS.mem_UJ_iff_adj_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:50.65133+00:00
-- url     : https://prove2.me/theorems/186bf318-9af8-5fe9-91a7-c024b90a3f54
-- title:
--   Reg SS: mem UJ iff adj mul
-- statement:
--   The Reg SS construction uses the mem UJ iff adj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L405-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L405-L412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.mem_UJ_iff_adj_mul (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det) (g : GL n A) :
    g ∈ UJ σ J ↔ adj σ J (g : Matrix n n A) * (g : Matrix n n A) = 1 := by sorry
