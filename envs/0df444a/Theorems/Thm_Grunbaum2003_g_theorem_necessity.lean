-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_necessity
-- name    : Grunbaum2003.g_theorem_necessity
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:49:33.01302+00:00
-- url     : https://prove2.me/theorems/a5d42b87-a93f-4ddc-ac1f-579bb1ba5476
-- title:
--   Necessity in the $g$-theorem (Stanley): the $g$-vector is an $M$-sequence
-- statement:
--   Let $d\ge 4$ and let $P\subseteq\mathbb R^d$ be a simplicial $d$-polytope with face numbers $f_0,\dots,f_{d-1}$. Then there is an $M$-sequence $g=(g_0,g_1,\dots,g_{\lfloor d/2\rfloor})$ such that
--
--   $$
--   f_j=\sum_{i=0}^{\lfloor d/2\rfloor} g_i\,m_{i,j+1}\qquad(0\le j\le d-1),
--   $$
--
--   where $M_d=(m_{ik})$ is Björner's matrix with entries $m_{ik}=\binom{d+1-i}{d+1-k}-\binom{i}{d+1-k}$. Being an $M$-sequence means $g_0=1$ and, for $1\le k\le\lfloor d/2\rfloor$, either $g_k=0$ or, writing the $k$-binomial expansion $g_k=\binom{a_k}{k}+\binom{a_{k-1}}{k-1}+\dots+\binom{a_i}{i}$ with $a_k>\dots>a_i\ge i\ge1$, one has $\binom{a_k-1}{k-1}+\dots+\binom{a_i-1}{i-1}\le g_{k-1}$.
--
--   This is the necessity half of the $g$-theorem, proved by Stanley (1980) via the hard Lefschetz theorem for projective toric varieties, and later by McMullen through the polytope algebra.
--
--   **Formalization Note** A $d$-polytope is a nonempty finite convex hull in $\mathbb R^d$ (`Fin d → ℝ`) with full affine span (`IsDPolytope`); faces are exposed subsets, and $f_k(P)$ (`faceCount P k`) counts nonempty exposed faces whose affine span has a $k$-dimensional direction.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §10.6, pp. 198a–198b (g-theorem in Björner's matrix formulation, necessity; R. P. Stanley, The number of faces of a simplicial convex polytope, Adv. Math. 35 (1980) 236–238)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_necessity (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
