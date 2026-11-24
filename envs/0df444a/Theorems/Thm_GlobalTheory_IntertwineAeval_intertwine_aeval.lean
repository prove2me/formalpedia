-- Prove2me | Theorems.Thm_GlobalTheory_IntertwineAeval_intertwine_aeval
-- name    : GlobalTheory.IntertwineAeval.intertwine_aeval
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:58.716632+00:00
-- url     : https://prove2.me/theorems/13f6acd4-ae19-46b8-922f-aca2a89ef0a3
-- title:
--   Intertwine Aeval: intertwine aeval
-- statement:
--   The Intertwine Aeval construction uses the intertwine aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntertwineAeval.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntertwineAeval.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntertwineAeval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwineAeval

theorem GlobalTheory.IntertwineAeval.intertwine_aeval {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (p : Polynomial ℂ) (v : M) :
    r (Polynomial.aeval T p v) = Polynomial.aeval T' p (r v) := by sorry
