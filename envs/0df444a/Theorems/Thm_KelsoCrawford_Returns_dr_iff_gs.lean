-- Prove2me | Theorems.Thm_KelsoCrawford_Returns_dr_iff_gs
-- name    : KelsoCrawford.Returns.dr_iff_gs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:17.362975+00:00
-- url     : https://prove2.me/theorems/6e79bde5-aa12-44d6-888b-28cbc5e977e8
-- title:
--   Theorem 6 — when workers are alike in production, (DR) and (GS) are equivalent
-- statement:
--   Let $W$ be a finite set of $m$ workers, and let a firm's technology treat the workers as alike in production: $y(C) = \bar y(|C|)$ for every $C \subseteq W$, for some $\bar y : \mathbb{N} \to \mathbb{R}$. Then the following are equivalent:
--
--   1. $\bar y$ has nonincreasing returns to workers (DR):
--   $$\bar y(w + 1) - \bar y(w) \le \bar y(w) - \bar y(w - 1) \qquad \text{for every integer } w,\ 1 \le w \le m - 1;$$
--   2. the technology $C \mapsto \bar y(|C|)$ satisfies the gross-substitutes condition (GS) for real salary vectors: whenever $C$ maximizes the profit $\bar y(|C|) - \sum_{i \in C} s_i$ at the salary vector $s$ and $\tilde s \ge s$, some profit-maximizing set at $\tilde s$ contains $\{ i \in C : \tilde s_i = s_i \}$.
--
--   The theorem identifies (GS), the hypothesis behind every existence result of the paper, with the textbook concavity condition in the case of identical workers, so that (GS) can be read as a generalization of nonincreasing returns to heterogeneous workers.
--
--   **Formalization Note** Salaries range over all of $\mathbb{R}^W$ (the continuous form of (GS)). Neither (MP) nor $\bar y(0) = 0$ is assumed, and none is needed. For $m \le 1$ condition (DR) is vacuous and (GS) holds, so no lower bound on $m$ is imposed. The range $1 \le w \le m - 1$ is written $1 \le w$, $w + 1 \le m$ over the natural numbers.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1499, Theorem 6

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology

namespace KelsoCrawford.Returns

theorem dr_iff_gs {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ) :
    DR (Fintype.card W) ybar ↔
      KelsoCrawford.Process.GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by sorry

end KelsoCrawford.Returns
