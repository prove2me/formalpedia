-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_analyticAt_mvPolynomial_eval
-- name    : GlobalTheory.SimpleRoots.analyticAt_mvPolynomial_eval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:09.985706+00:00
-- url     : https://prove2.me/theorems/e235d89f-2af1-48c7-a1e5-bec162cd349b
-- title:
--   Simple Roots: analytic At mv Polynomial eval
-- statement:
--   The Simple Roots construction uses the analytic At mv Polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}

theorem GlobalTheory.SimpleRoots.analyticAt_mvPolynomial_eval (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x := by sorry
