-- Prove2me | Theorems.Thm_GlobalTheory_AnalyticLineDerivative_hasDerivAt_line
-- name    : GlobalTheory.AnalyticLineDerivative.hasDerivAt_line
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:56:38.052007+00:00
-- url     : https://prove2.me/theorems/0490b27b-dab7-4f95-8a65-b67c5dc4bae2
-- title:
--   Analytic Line Derivative: has Deriv At line
-- statement:
--   The Analytic Line Derivative construction uses the has Deriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/Imports.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/Imports.lean#L9-L42

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

theorem GlobalTheory.AnalyticLineDerivative.hasDerivAt_line {S : Type*} {J : Type*} [CommRing S] [Fintype J] (φ : S →+* ℂ)
    (u v : J → ℂ) (p : MvPolynomial J S) :
    HasDerivAt (fun t : ℂ => eval₂Hom φ (u + t • v) p)
      (∑ j, v j * eval₂Hom φ u (pderiv j p)) 0 := by sorry
