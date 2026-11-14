-- Prove2me | Theorems.Thm_LatticePrepro_exists_base
-- name    : LatticePrepro.exists_base
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:55.420235+00:00
-- url     : https://prove2.me/theorems/93afdbbc-d40e-46a2-acbf-add30a08a114
-- title:
--   A base $B \ge 2$ with $Y \le B^m \le 2^m Y$
-- statement:
--   For all natural numbers $m \ge 1$ and $Y \ge 1$ there is an integer $B \ge 2$ such that
--   $$Y \le B^m \le 2^m \cdot Y.$$
--
--   In the size–gap tradeoff of Theorem 4.8, the explicit moment representation has moment parameter $r = B^m$, where $B \ge 2$ is chosen with $B^m \ge 8 N g$ for $N$ the number of evaluation tables and $g$ the gap (the paper takes the least such $B$). The lower bound gives the hypothesis $2 g N < r$ of Theorem 4.6, and the upper bound $B^m \le 2^m \cdot 8 N g$ controls the number of columns of the resulting linear system.
--
--   **Formalization Note**: All quantities are natural numbers; the lemma only asserts the existence of such a $B$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Theorem 4.8 (\label{thm:quantitative-affine-gap}); Lean: LatticePrepro/Basic/Nat.lean, LatticePrepro.exists_base

import Mathlib

theorem LatticePrepro.exists_base {Y m : ℕ} (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m ∧ B ^ m ≤ 2 ^ m * Y := by sorry
