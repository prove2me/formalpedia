-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_eq_of_contr
-- name    : GlobalTheory.RegBound.eq_of_contr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:01.759317+00:00
-- url     : https://prove2.me/theorems/0de23c75-3eb9-43ba-ab72-9d3289e18ca7
-- title:
--   Reg Bound: eq of contr
-- statement:
--   The Reg Bound construction uses the eq of contr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L466-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L466-L471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.RegBound.eq_of_contr {F G : MvPolynomial σ L} (h : ∀ φ : L →ₗ[K] K, contr φ F = contr φ G) :
    F = G := by sorry
