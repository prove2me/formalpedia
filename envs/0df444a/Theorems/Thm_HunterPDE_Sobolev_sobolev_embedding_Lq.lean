-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_sobolev_embedding_Lq
-- name    : HunterPDE.Sobolev.sobolev_embedding_Lq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:14:47.972461+00:00
-- url     : https://prove2.me/theorems/513d3fcc-e5ba-4f2b-bd7b-76a85e79a1fb
-- title:
--   Theorem 3.31 — W^{1,p}(ℝⁿ) ↪ L^q(ℝⁿ) for p ≤ q ≤ p*
-- statement:
--   Let $1 \le p < n$ and $p \le q \le p^*$, where $p^* = np/(n-p)$ is the Sobolev conjugate of $p$. Then $W^{1,p}(\mathbb{R}^n) \hookrightarrow L^q(\mathbb{R}^n)$: there is a constant $C = C(n, p, q)$ such that every $f \in W^{1,p}(\mathbb{R}^n)$ belongs to $L^q(\mathbb{R}^n)$ and
--   $$\|f\|_q \le C\, \|f\|_{W^{1,p}} .$$
--
--   This is the Sobolev embedding theorem for $p < n$ on the whole space, obtained from Theorem 3.28 at $q = p^*$ by density (Theorem 3.24), and from interpolation between $L^p$ and $L^{p^*}$ for intermediate $q$.
--
--   **Formalization Note.** $W^{1,p}(\mathbb{R}^n)$ and its norm are those of Definition 3.23 (`MemW 1 p univ`, `sobolevNorm 1 p univ`). The constant is a nonnegative real chosen after $n, p, q$ and before $f$. The standing assumption $n \ge 2$ of §3.7 is implied by $1 \le p < n$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 66, Theorem 3.31

import Mathlib
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Definitions.Def_HunterPDE_Sobolev_SobolevConjugate

open MeasureTheory

namespace HunterPDE.Sobolev

/-- Theorem 3.31 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 66: if `1 ≤ p < n` and
`p ≤ q ≤ p*`, then `W^{1,p}(ℝⁿ) ↪ L^q(ℝⁿ)`: there is a constant `C = C(n, p, q)` such that every
`f ∈ W^{1,p}(ℝⁿ)` lies in `L^q(ℝⁿ)` with `‖f‖_q ≤ C ‖f‖_{W^{1,p}}`. The constant is chosen after
`n, p, q` and before `f`. -/
theorem sobolev_embedding_Lq {n : ℕ} {p q : ℝ} (hp : 1 ≤ p) (hpn : p < n) (hpq : p ≤ q)
    (hq : q ≤ sobolevConjugate n p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW 1 (ENNReal.ofReal p) Set.univ f →
        MemLp f (ENNReal.ofReal q) volume ∧
          eLpNorm f (ENNReal.ofReal q) volume ≤
            (C : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by sorry

end HunterPDE.Sobolev
