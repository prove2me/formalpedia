-- Prove2me | Theorems.Thm_GlobalTheory_SepPoint_exists_ev
-- name    : GlobalTheory.SepPoint.exists_ev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:16.196819+00:00
-- url     : https://prove2.me/theorems/0377c079-51e6-41f1-896b-0d76bd7ce2cc
-- title:
--   Sep Point: exists ev
-- statement:
--   The Sep Point construction uses the exists ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegrallyClosedAdjoin.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegrallyClosedAdjoin.lean#L23-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SepPoint

theorem GlobalTheory.SepPoint.exists_ev (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) (H : Algebra.adjoin k (s : Set F)) (hH : H ≠ 0) :
    ∃ ev : Algebra.adjoin k (s : Set F) →ₐ[k] SeparableClosure k, ev H ≠ 0 := by sorry
