-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_g_theorem_pos_dim_tail
-- name    : Grunbaum2003.simplicial_g_theorem_pos_dim_tail
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:38.39399+00:00
-- url     : https://prove2.me/theorems/fe689a4a-f2eb-4ff9-aa33-3ccb02ca757c
-- title:
--   Positive-dimension Billera–Lee–Stanley $g$-theorem for normalized $f$-vectors ($f_0 = 1$)
-- statement:
--   This theorem states the Billera–Lee (sufficiency) and Stanley (necessity) $g$-theorem in positive ambient dimension $d \ge 1$ for an extended integer vector $f = (f_0, f_1, \dots, f_d) : \operatorname{Fin}(d + 1) \to \mathbb{Z}$ normalized by $f_0 = 1$ (corresponding to $f_{-1} = 1$).
--
--   Let $d \ge 1$ be a positive integer and let $f : \operatorname{Fin}(d + 1) \to \mathbb{Z}$ satisfy $f(0) = 1$. Then there exists a simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsSimplicialDPolytope P`) with $f(j + 1) = f_j(P)$ for all $0 \le j < d$ if and only if there exists an $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ of length $\lfloor d/2 \rfloor + 1$ (`IsMSequence (d / 2) g`) such that
--
--   $$
--   \forall k \in \{0, \dots, d\},\quad f(k) = \sum_{j=0}^{\lfloor d/2 \rfloor} g_j \left(\binom{d + 1 - j}{d + 1 - k} - \binom{j}{d + 1 - k}\right).
--   $$
--
--   Combining this theorem for $d \ge 1$ with `gTheoremMatrix_col_zero_sum_and_zero_dim` (which handles $d = 0$ completely and proves $\sum_{j=0}^{\lfloor d/2 \rfloor} g_j M_d(j, 0) = g_0 = 1$ to recover $f(0) = 1$ in the backward direction) yields the full characterization `simplicial_g_theorem` for all $d \in \mathbb{N}$.
--
--   **Formalization Note** Separating the normalization identity $f(0) = g_0 = 1$ and the degenerate $d = 0$ case in `gTheoremMatrix_col_zero_sum_and_zero_dim` isolates the substantive Macaulay-bound and Gale-diagram/shelling constructions to $d \ge 1$ with $f(0) = 1$ fixed.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_g_theorem_pos_dim_tail (d : ℕ) (hd : 0 < d)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val := by sorry

end Grunbaum2003
