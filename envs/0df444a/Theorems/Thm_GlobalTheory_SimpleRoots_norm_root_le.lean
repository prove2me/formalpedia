-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_norm_root_le
-- name    : GlobalTheory.SimpleRoots.norm_root_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:35.170877+00:00
-- url     : https://prove2.me/theorems/0d52addc-df5e-42e6-8c91-ad196cf26c0a
-- title:
--   Simple Roots: norm root le
-- statement:
--   The Simple Roots construction uses the norm root le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L162-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L162-L171

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

theorem GlobalTheory.SimpleRoots.norm_root_le {P : ℂ[X]} (hP : P.Monic) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ M) {y : ℂ} (hy : P.eval y = 0) : ‖y‖ ≤ M + 1 := by sorry
