-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_segments_greedy
-- name    : OnlineRandomization.Restart.segments_greedy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:34.880728+00:00
-- url     : https://prove2.me/theorems/9dc09889-c7b8-431a-b296-16f88df0f54a
-- title:
--   Proof of Theorem 4.1, p. 18 — the restart algorithm cuts $r$ into successive longest prefixes in $R_H$
-- statement:
--   Let $F$ be a request-answer game with finite nonempty answer set, let $H$ be a real number with $f_0 \le H$, and let $r$ be a nonempty request sequence. Let $r(1), \dots, r(t)$ be the segments of the restart algorithm on $r$. Then $r(1)$ is the longest prefix of $r$ that lies in $R_H$:
--
--   $$r(1) \ne \emptyset,\quad r(1) \text{ is a prefix of } r,\quad r(1) \in R_H,\quad |p| \le |r(1)| \text{ for every prefix } p \text{ of } r \text{ in } R_H,$$
--
--   and $r(2), \dots, r(t)$ are exactly the segments of the restart algorithm on the suffix of $r$ obtained by deleting $r(1)$.
--
--   By induction, the online rule of the restart algorithm produces the page's decomposition: $r(1)$ is the longest prefix of $r$ in $R_H$, $r(2)$ the longest prefix in $R_H$ of the remaining suffix, and so forth.
--
--   **Formalization Note** The hypothesis $f_0 \le H$ (Lean: `F.cost [] [] ≤ H`) makes every one-request sequence belong to $R_H$; without it the page's longest prefix in $R_H$ could be empty and the decomposition would not advance. In Theorem 4.1 it follows from $f_0 \ge 0$ and the diameter bound, since $f_0 = |\delta((\emptyset,\emptyset),(\emptyset,\emptyset))| \le D \le H$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 18, §4, proof of Theorem 4.1, second paragraph, sentence 2

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- p. 18: the restart rule decomposes `r` greedily: when `f_0 ≤ H`, the first segment `r(1)`
of a nonempty `r` is the longest prefix of `r` lying in `R_H`, and the remaining segments are
the decomposition of the suffix obtained by deleting `r(1)`. -/
theorem segments_greedy {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (hf0 : F.cost [] [] ≤ H) (r : List R) (hr : r ≠ []) :
    ∃ s : List R, segments F H r = s :: segments F H (r.drop s.length) ∧
      s ≠ [] ∧ s <+: r ∧ InRH F H s ∧
      ∀ p : List R, p <+: r → InRH F H p → p.length ≤ s.length := by sorry

end OnlineRandomization.Restart
