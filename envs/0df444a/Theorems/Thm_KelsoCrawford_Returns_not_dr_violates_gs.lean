-- Prove2me | Theorems.Thm_KelsoCrawford_Returns_not_dr_violates_gs
-- name    : KelsoCrawford.Returns.not_dr_violates_gs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:55.752119+00:00
-- url     : https://prove2.me/theorems/79cc250e-783b-4811-9801-e917758e87e3
-- title:
--   Theorem 6, second half (pp. 1499–1500) — increasing returns at some w, as in (19), violate gross substitutes
-- statement:
--   Let $W$ be a finite set of $m$ workers and $y(C) = \bar y(|C|)$ a technology under which workers are alike in production. Suppose (DR) fails: there is an integer $w$ with $1 \le w \le m - 1$ such that
--   $$\bar y(w + 1) - \bar y(w) > \bar y(w) - \bar y(w - 1). \tag{19}$$
--   Then the technology $C \mapsto \bar y(|C|)$ does **not** satisfy the gross-substitutes condition (GS) for real salary vectors: there are salary vectors $s \le \tilde s$ and a profit-maximizing set at $s$ such that no profit-maximizing set at $\tilde s$ contains all of its members whose salaries did not change.
--
--   This is the direction "(GS) implies (DR)" of Theorem 6, in the contrapositive form in which the paper proves it.
--
--   **Formalization Note** The range $1 \le w \le m - 1$ is written $1 \le w$ and $w + 1 \le m$ over the natural numbers, so that $w - 1$ never truncates. Salaries range over all of $\mathbb{R}^W$.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1499–1500, proof of Theorem 6, second paragraph (eq. (19))

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology

namespace KelsoCrawford.Returns

theorem not_dr_violates_gs {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ)
    (h19 : ∃ w : ℕ, 1 ≤ w ∧ w + 1 ≤ Fintype.card W ∧
      ybar w - ybar (w - 1) < ybar (w + 1) - ybar w) :
    ¬ KelsoCrawford.Process.GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by sorry

end KelsoCrawford.Returns
