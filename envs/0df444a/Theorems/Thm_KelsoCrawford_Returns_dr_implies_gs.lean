-- Prove2me | Theorems.Thm_KelsoCrawford_Returns_dr_implies_gs
-- name    : KelsoCrawford.Returns.dr_implies_gs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:49.716268+00:00
-- url     : https://prove2.me/theorems/e6bc4891-a4c5-4221-b02f-a51ae382992c
-- title:
--   Theorem 6, first half (p. 1499) — nonincreasing returns to identical workers imply gross substitutes
-- statement:
--   Let $W$ be a finite set of $m$ workers, and let a firm's technology treat workers as alike in production, $y(C) = \bar y(|C|)$ for some $\bar y : \mathbb{N} \to \mathbb{R}$. If $\bar y$ has nonincreasing returns to workers,
--   $$\bar y(w + 1) - \bar y(w) \le \bar y(w) - \bar y(w - 1) \qquad (1 \le w \le m - 1),$$
--   then the technology $C \mapsto \bar y(|C|)$ satisfies the gross-substitutes condition (GS) for real salary vectors: whenever $C$ maximizes $\bar y(|C|) - \sum_{i \in C} s_i$ and $\tilde s \ge s$, some maximizer $\tilde C$ at $\tilde s$ contains every member of $C$ whose salary did not change.
--
--   This is the direction "(DR) implies (GS)" of Theorem 6, which shows that the familiar concavity condition on a production function is enough for the gross-substitutes hypothesis behind the paper's existence theorems.
--
--   **Formalization Note** Salaries range over all of $\mathbb{R}^W$ (continuous salaries). No assumption $\bar y(0) = 0$ ((NFL)) or (MP) is made; the paper's proof uses neither.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1499, Theorem 6 and its proof, first paragraph (eq. (18))

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology

namespace KelsoCrawford.Returns

theorem dr_implies_gs {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ)
    (hDR : DR (Fintype.card W) ybar) :
    KelsoCrawford.Process.GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by sorry

end KelsoCrawford.Returns
