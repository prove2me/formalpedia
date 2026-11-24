-- Prove2me | Theorems.Thm_GlobalTheory_AnalyticLineDerivative_analyticAt_eval
-- name    : GlobalTheory.AnalyticLineDerivative.analyticAt_eval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:56:31.228979+00:00
-- url     : https://prove2.me/theorems/0d9ac01d-397f-4886-9d45-ad3f9ae1d063
-- title:
--   Analytic Line Derivative: analytic At eval
-- statement:
--   The Analytic Line Derivative construction uses the analytic At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/Imports.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/Imports.lean#L44-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticLineDerivative
open MvPolynomial
universe u_1 u_2 u_3 u_4

theorem GlobalTheory.AnalyticLineDerivative.analyticAt_eval {E : Type*} {S : Type*} {J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CommRing S] [Fintype J] (χ : E → S →+* ℂ) (z₀ : E) (u₀ : J → ℂ)
    (h : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀) (p : MvPolynomial J S) :
    AnalyticAt ℂ (fun w : E × (J → ℂ) => eval₂Hom (χ w.1) w.2 p) (z₀, u₀) := by sorry
