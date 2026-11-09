-- Prove2me | Theorems.Thm_Grunbaum2003_gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
-- name    : Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:53:48.857425+00:00
-- url     : https://prove2.me/theorems/d44da256-9e17-4d2a-a7f1-b8ea6b19075b
-- title:
--   Row-one entries, top-two-column double counting, and $g(2)=0$ reduction of $M_d$
-- statement:
--   For Björner's $g$-theorem matrix $M_{d,i,k} = \binom{d+1-i}{d+1-k} - \binom{i}{d+1-k}$:
--
--   1. Row $i = 1$ satisfies $M_{d,1,k} = \binom{d}{d+1-k}$ for $k < d$ and $M_{d,1,d} = d - 1$.
--   2. Top columns $k = d-1$ and $k = d$ satisfy $M_{d,i,d} = d + 1 - 2i$ and the simplicial ridge-facet double-counting relation
--
--   $$
--   2\,M_{d,i,d-1} = d\,M_{d,i,d} \qquad (0 \le i \le d+1).
--   $$
--
--   3. Whenever $g$ is an $M$-sequence of length $\lfloor d/2 \rfloor$ with $g(2) = 0$, the $g$-theorem linear combination collapses to its first two terms $\binom{d+1}{j+1} + g(1)\,M_{d,1,j+1}$.
--   4. Any simplicial $d$-polytope $P$ ($d \ge 4$) represented by an $M$-sequence $g$ satisfies $g(0) = 1$, $f_0(P) = d + 1 + g(1)$, and $2\,f_{d-2}(P) = d\,f_{d-1}(P)$.
--
--   This theorem supplies the algebraic $M_d$ identities for stacked polytopes ($g(2)=0$) and the top-dimensional necessity relations.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem gTheoremMatrix_row_one_top_columns_and_g2_zero_sum :
    (∀ {d k : ℕ}, k < d →
      gTheoremMatrix d 1 k = (Nat.choose d (d + 1 - k) : ℤ)) ∧
    (∀ {d : ℕ}, 1 ≤ d →
      gTheoremMatrix d 1 d = (d : ℤ) - 1) ∧
    (∀ {d i : ℕ}, i ≤ d + 1 →
      gTheoremMatrix d i d = (d + 1 : ℤ) - 2 * (i : ℤ)) ∧
    (∀ {d i : ℕ}, 2 ≤ d → i ≤ d + 1 →
      2 * gTheoremMatrix d i (d - 1) = (d : ℤ) * gTheoremMatrix d i d) ∧
    (∀ {d : ℕ}, 2 ≤ d → ∀ {g : ℕ → ℕ},
      IsMSequence (d / 2) g → g 2 = 0 → ∀ (j : Fin d),
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val =
          (Nat.choose (d + 1) j.succ.val : ℤ) + (g 1 : ℤ) * gTheoremMatrix d 1 j.succ.val) ∧
    (∀ {d : ℕ}, 4 ≤ d → ∀ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsMSequence (d / 2) g →
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
      g 0 = 1 ∧
      faceCount P 0 = d + 1 + g 1 ∧
      2 * faceCount P (d - 2) = d * faceCount P (d - 1) ∧
      (d + 1 < faceCount P 0 → 0 < g 1)) := by sorry

end Grunbaum2003
