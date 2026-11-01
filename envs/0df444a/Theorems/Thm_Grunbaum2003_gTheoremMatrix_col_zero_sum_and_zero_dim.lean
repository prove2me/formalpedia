-- Prove2me | Theorems.Thm_Grunbaum2003_gTheoremMatrix_col_zero_sum_and_zero_dim
-- name    : Grunbaum2003.gTheoremMatrix_col_zero_sum_and_zero_dim
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:33.728424+00:00
-- url     : https://prove2.me/theorems/84c25eb1-472e-433d-8a34-158bce7151db
-- title:
--   Column-zero identity for the $g$-theorem matrix and the zero-dimensional $g$-theorem
-- statement:
--   This theorem establishes the column-zero projection identity for the $g$-theorem transformation matrix $M_d$ in arbitrary dimension $d \ge 0$, together with the complete characterization of $f$-vectors of simplicial $0$-polytopes (`simplicial_g_theorem` at $d = 0$).
--
--   For integers $d, j, k \in \mathbb{N}$, the $g$-theorem matrix entry (`gTheoremMatrix d j k`) is defined by
--
--   $$
--   M_d(j, k) = \binom{d + 1 - j}{d + 1 - k} - \binom{j}{d + 1 - k}.
--   $$
--
--   This theorem proves two assertions:
--
--   1. For every dimension $d \in \mathbb{N}$ and every sequence $g : \mathbb{N} \to \mathbb{N}$, evaluating the linear combination at column $k = 0$ extracts $g_0$:
--
--   $$
--   \sum_{j=0}^{\lfloor d/2 \rfloor} g_j \, M_d(j, 0) = g_0.
--   $$
--
--   2. In dimension $d = 0$, a vector $f : \operatorname{Fin} 1 \to \mathbb{Z}$ satisfies $f_0 = 1$ and is realized by a simplicial $0$-polytope $P \subseteq \mathbb{R}^0$ if and only if there exists an $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ (`IsMSequence 0 g`) such that $f_k = \sum_{j=0}^{0} g_j \, M_0(j, k)$ for all $k \in \operatorname{Fin} 1$.
--
--   The column-zero identity explains why the normalization $f_0 = 1$ (representing $f_{-1} = 1$) corresponds under $M_d$ to the initial condition $g_0 = 1$ of an $M$-sequence in the Billera–Lee and Stanley $g$-theorem.
--
--   **Formalization Note** For $1 \le j \le \lfloor d/2 \rfloor$, both $d + 1 - j < d + 1$ and $j < d + 1$ hold, so both binomial coefficients in $M_d(j, 0)$ vanish, leaving $M_d(0, 0) = \binom{d+1}{d+1} - \binom{0}{d+1} = 1$.
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

theorem gTheoremMatrix_col_zero_sum_and_zero_dim :
    (∀ (d : ℕ) (g : ℕ → ℕ),
      ∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0 = (g 0 : ℤ)) ∧
    (∀ f : Fin 1 → ℤ,
      (f 0 = 1 ∧ ∃ P : Set (Fin 0 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 0, f j.succ = (faceCount P j.val : ℤ)) ↔
      ∃ g : ℕ → ℕ, IsMSequence 0 g ∧
        ∀ k : Fin 1,
          f k = ∑ j ∈ Finset.range 1,
            (g j : ℤ) * gTheoremMatrix 0 j k.val) := by sorry

end Grunbaum2003
