-- Prove2me | Theorems.Thm_OfflineToOnline_orthant_dist_iff
-- name    : OfflineToOnline.orthant_dist_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:56.561821+00:00
-- url     : https://prove2.me/theorems/a253fb29-c02f-43f2-9954-fc37300e1040
-- title:
--   p.21 display — for the orthant, $d_\infty(\frac1T\sum_t u_t,S)\le g$ iff every coordinate sum is $\ge -Tg$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be the nonnegative orthant, $T\ge1$ and $g\ge0$. For all vectors $u_1,\dots,u_T\in\mathbb R^d$,
--
--   $$
--   d_\infty\Big(\frac1T\sum_{t=1}^Tu_t,\ S\Big)\le g\quad\Longleftrightarrow\quad\forall j:\ \Big[\sum_{t=1}^Tu_t\Big]_j\ge-Tg .
--   $$
--
--   In the proof of Theorem 2, with $u_t=\boldsymbol p(\theta_t^{(i)},\mathrm{AdvB}(z_t^{(i-1)},f_t))$, this converts the approachability guarantee of each Blackwell algorithm into the coordinatewise slack condition of Definition 6.
--
--   Differences from the source:
--   - generalization: u_t = p(θ_t^(i), AdvB(z_t^(i−1), f_t)) for the run of Online-IG → any vectors u_t; reason: the equivalence holds for all vectors; the page's are a special case
--   - encoding: a rate g(T); rounds t = 1..T → g ≥ 0 and T ≥ 1; rounds 0..T−1; reason: g(T) is a nonnegative rate; for g < 0 the left side is false and the right side can hold
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, proof of Theorem 2, p.21

import Mathlib
import Definitions.Def_OfflineToOnline_orthant

namespace OfflineToOnline

/-- **p.21 display**, the orthant equivalence: for the nonnegative orthant `S ⊆ ℝ^d`, `T ≥ 1`,
`g ≥ 0` and vectors `u_1, …, u_T`,
`d∞((1/T) ∑_t u_t, S) ≤ g ⟺ ∀ j, [∑_t u_t]_j ≥ −T g`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, proof of Theorem 2, p.21 ("Because the target set S is the positive orthant, we have …").

Formalization Note: on the page `u_t = p(θ_t^(i), AdvB(z_t^(i−1), f_t))` (printed `z_t^{i−1}`);
the equivalence holds for any vectors. `g = g(T) ≥ 0` is a rate; for `g < 0` the left side is
false and the right side can hold. `d∞` is `Metric.infDist` in `Fin d → ℝ`. Rounds are
`0, …, T − 1`. -/
theorem orthant_dist_iff (d T : ℕ) (hT : 1 ≤ T) (g : ℝ) (hg : 0 ≤ g) (u : ℕ → Fin d → ℝ) :
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, u t) (orthant d) ≤ g ↔
      ∀ j, -(T * g) ≤ ∑ t ∈ Finset.range T, u t j := by sorry

end OfflineToOnline
