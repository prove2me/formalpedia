-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_analyticAt_eval_map
-- name    : GlobalTheory.SimpleRoots.analyticAt_eval_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:03.329831+00:00
-- url     : https://prove2.me/theorems/ab094cb6-7afe-4113-90d2-f6ce46133760
-- title:
--   Simple Roots: analytic At eval map
-- statement:
--   The Simple Roots construction uses the analytic At eval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L18-L22

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

theorem GlobalTheory.SimpleRoots.analyticAt_eval_map (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by sorry
