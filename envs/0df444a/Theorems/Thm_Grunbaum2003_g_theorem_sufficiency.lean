-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_sufficiency
-- name    : Grunbaum2003.g_theorem_sufficiency
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-08T20:49:30.814138+00:00
-- url     : https://prove2.me/theorems/83abae38-ed00-4bd8-b1a6-b0250e869010
-- title:
--   Sufficiency in the $g$-theorem (Billera–Lee): every $M$-sequence is realised
-- statement:
--   Let $d\ge 4$ and let $g=(g_0,\dots,g_{\lfloor d/2\rfloor})$ be an $M$-sequence. Then there is a simplicial $d$-polytope $P\subseteq\mathbb R^d$ whose face numbers are
--
--   $$
--   f_j(P)=\sum_{i=0}^{\lfloor d/2\rfloor} g_i\,m_{i,j+1}\qquad(0\le j\le d-1),
--   $$
--
--   where $m_{ik}=\binom{d+1-i}{d+1-k}-\binom{i}{d+1-k}$ are the entries of Björner's matrix $M_d$. The $M$-sequence condition is the one of `IsMSequence`: $g_0=1$ and, for $1\le k\le\lfloor d/2\rfloor$, either $g_k=0$ or the lower shadow $\binom{a_k-1}{k-1}+\dots+\binom{a_i-1}{i-1}$ of the $k$-binomial expansion of $g_k$ is at most $g_{k-1}$.
--
--   This is the sufficiency half of the $g$-theorem, proved by Billera and Lee (1981) by an explicit construction of polytopes realising each $M$-sequence.
--
--   **Formalization Note** A $d$-polytope is a nonempty finite convex hull in $\mathbb R^d$ (`Fin d → ℝ`) with full affine span (`IsDPolytope`); faces are exposed subsets, and $f_k(P)$ (`faceCount P k`) counts nonempty exposed faces whose affine span has a $k$-dimensional direction.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §10.6, pp. 198a–198b (g-theorem in Björner's matrix formulation, sufficiency; L. J. Billera and C. W. Lee, A proof of the sufficiency of McMullen's conditions for f-vectors of simplicial convex polytopes, J. Combin. Theory Ser. A 31 (1981) 237–255)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_sufficiency (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
