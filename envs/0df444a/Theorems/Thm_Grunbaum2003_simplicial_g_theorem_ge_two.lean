-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_g_theorem_ge_two
-- name    : Grunbaum2003.simplicial_g_theorem_ge_two
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:28.643723+00:00
-- url     : https://prove2.me/theorems/e7ae1e2f-6a37-44e1-8033-40ccc5198bf4
-- title:
--   Higher-dimensional Billera–Lee–Stanley $g$-theorem ($d \ge 2$)
-- statement:
--   This theorem states the Billera–Lee (1980, 1981) sufficiency and Stanley (1980) necessity of McMullen's $g$-conjecture in dimensions $d \ge 2$ for normalized extended $f$-vectors $f : \operatorname{Fin}(d + 1) \to \mathbb{Z}$ with $f(0) = 1$.
--
--   Let $d \ge 2$ be an integer and let $f : \operatorname{Fin}(d + 1) \to \mathbb{Z}$ satisfy $f(0) = 1$. Then there exists a simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsSimplicialDPolytope P`) with $f(j + 1) = f_j(P)$ for all $0 \le j < d$ if and only if there exists an $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ of length $\lfloor d/2 \rfloor + 1$ (`IsMSequence (d / 2) g`) such that
--   $$
--   \forall k \in \{0, \dots, d\},\quad f(k) = \sum_{j=0}^{\lfloor d/2 \rfloor} g_j \left(\binom{d + 1 - j}{d + 1 - k} - \binom{j}{d + 1 - k}\right).
--   $$
--
--   Together with the proved $d = 1$ theorem `simplicial_g_theorem_one_dim`, this immediately yields `simplicial_g_theorem_pos_dim_tail` for all $d \ge 1$.
--
--   **Formalization Note** Isolating $d \ge 2$ ensures that $\lfloor d/2 \rfloor \ge 1$ and that proper faces include both vertices and edges, matching the hypothesis regime of the Billera–Lee shellable subdivision construction and Stanley's toric Hard Lefschetz theorem.
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

theorem simplicial_g_theorem_ge_two (d : ℕ) (hd : 2 ≤ d)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val := by sorry

end Grunbaum2003
