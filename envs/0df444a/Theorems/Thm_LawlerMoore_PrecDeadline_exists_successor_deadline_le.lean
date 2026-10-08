-- Prove2me | Theorems.Thm_LawlerMoore_PrecDeadline_exists_successor_deadline_le
-- name    : LawlerMoore.PrecDeadline.exists_successor_deadline_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:27:48.206112+00:00
-- url     : https://prove2.me/theorems/5c2fdd04-6414-426b-b22d-1a04580171b8
-- title:
--   Section 2, proof of the Theorem — if $\bar d_j < \bar d_i$, then $j$ or a successor of $j$ has a deadline at least as early as $i$'s
-- statement:
--   Let $n$ jobs carry real deadlines $d_1,\dots,d_n$, let $\rho$ be a precedence relation, and let $\bar d_j = \min\{d_k \mid k = j \text{ or } j\rho k\} + j\varepsilon$ be the modified deadlines. Assume $\varepsilon$ is a **small positive number** in the sense
--
--   $$
--   \varepsilon > 0 \quad\text{and}\quad n\varepsilon < d_l - d_k \ \text{ whenever } d_k < d_l ,
--   $$
--
--   i.e. $n\varepsilon$ is smaller than every positive difference between two deadlines. Then for any jobs $i, j$ with $\bar d_j < \bar d_i$ there is a job $k$ that is $j$ itself or a successor of $j$ ($j\rho k$) with
--
--   $$
--   d_k \le d_i .
--   $$
--
--   In the proof of the §2 Theorem this is what allows two adjacent jobs $i, j$ with $\bar d_i > \bar d_j$ to be interchanged without making $i$ late.
--
--   **Formalization Note** The paper states this for a consecutive pair $i, j$ of a sequence; the claim does not depend on the sequence, so it is stated for any two jobs. The paper's "$\varepsilon$ is a small number" is made explicit as the displayed condition; it is needed here (with a large $\varepsilon$ the tie-breaking term can outweigh a difference of deadlines). No property of $\rho$ is used, because the definition of $\bar d_j$ already counts $j$ among its own successors. Jobs are `Fin n`, 0-based.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 78, Section 2, proof of the Theorem

import Mathlib
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem exists_successor_deadline_le (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (i j : Fin n) (hlt : modifiedDeadline ρ d ε j < modifiedDeadline ρ d ε i) :
    ∃ k, (k = j ∨ ρ j k) ∧ d k ≤ d i := by sorry

end LawlerMoore.PrecDeadline
