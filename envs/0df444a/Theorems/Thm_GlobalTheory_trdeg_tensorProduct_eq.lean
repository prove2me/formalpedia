-- Prove2me | Theorems.Thm_GlobalTheory_trdeg_tensorProduct_eq
-- name    : GlobalTheory.trdeg_tensorProduct_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:45.873254+00:00
-- url     : https://prove2.me/theorems/688568c0-3c7d-4c23-86a3-0e639301ca3c
-- title:
--   Global Theory: trdeg tensor Product eq
-- statement:
--   The Global Theory construction uses the trdeg tensor Product eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TrdegComplexBaseChangeEq.lean#L22-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TrdegComplexBaseChangeEq.lean#L22-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TrdegComplexBaseChangeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.trdeg_tensorProduct_eq {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsDomain (K ⊗[k] L)] : Algebra.trdeg K (K ⊗[k] L) = Algebra.trdeg k L := by sorry
