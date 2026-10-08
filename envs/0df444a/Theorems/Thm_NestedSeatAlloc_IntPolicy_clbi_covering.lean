-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_covering
-- name    : NestedSeatAlloc.IntPolicy.clbi_covering
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:38:53.881998+00:00
-- url     : https://prove2.me/theorems/9eb5d497-e017-42de-94f8-ab1302c48e6d
-- title:
--   p. 132 — covering property of CLBI functions: δ₊g(s₂) < c < δ₋g(s₁) gives an integer n ∈ [s₁, s₂] with c ∈ δg(n)
-- statement:
--   Let $g : \mathbb R \to \mathbb R$ be CLBI (concave on $s \ge 0$ and linear between consecutive nonnegative integers). For $t \ge 0$ write $\delta_+ g(t)$ and $\delta_- g(t)$ for the right and left derivatives, with the convention $\delta_- g(0) = +\infty$, and let $\delta g(t) = [\delta_+ g(t), \delta_- g(t)]$ be the subdifferential.
--
--   Let $0 \le s_1 < s_2$ and let $c$ be a constant with
--   $$\delta_+ g(s_2) < c < \delta_- g(s_1).$$
--   Then there is an integer $n$ with $s_1 \le n \le s_2$ and
--   $$c \in \delta g(n).$$
--
--   This is the device that turns the first-order condition (20) into an integer protection level: once the right derivative of the expected revenue drops below the next fare for large seat counts, the next fare is a subgradient at some integer.
--
--   **Formalization Note** The hypothesis $\delta_+ g(s_2) < c$ is stated as: the right derivative of $g$ at $s_2$ exists and is less than $c$. The hypothesis $c < \delta_- g(s_1)$ is stated as: $s_1 = 0$, or the left derivative at $s_1$ exists and exceeds $c$. The conclusion $c \in \delta g(n)$ requires the one-sided derivatives at $n$ to exist (both exist for a CLBI function at nonnegative integers) and $\delta_+ g(n) \le c \le \delta_- g(n)$, the left inequality being void at $n = 0$. The points are restricted to $s \ge 0$ because CLBI is a property on $s \ge 0$, where the paper applies it.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), §3, covering property of CLBI functions, p. 132 (italic statement preceding Theorem 2)

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

/-- Covering property of CLBI functions (p. 132): if `g` is CLBI and `δ₊g(s₂) < c < δ₋g(s₁)` for some
`0 ≤ s₁ < s₂` (with `δ₋g(0) = +∞`), then there is an integer `n ∈ [s₁, s₂]` with `c ∈ δg(n)`. -/
theorem clbi_covering (g : ℝ → ℝ) (hg : IsCLBI g) (s₁ s₂ c : ℝ) (h0 : 0 ≤ s₁) (h12 : s₁ < s₂)
    (hr : ∃ r, HasDerivWithinAt g r (Set.Ici s₂) s₂ ∧ r < c)
    (hl : s₁ = 0 ∨ ∃ l, HasDerivWithinAt g l (Set.Iic s₁) s₁ ∧ c < l) :
    ∃ n : ℕ, s₁ ≤ n ∧ (n : ℝ) ≤ s₂ ∧ InSubdiff g n c := by sorry

end NestedSeatAlloc.IntPolicy
