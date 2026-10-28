-- Prove2me | Theorems.Thm_InfoRelaxTS_Asymptotic_display_109
-- name    : InfoRelaxTS.Asymptotic.display_109
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:08.086797+00:00
-- url     : https://prove2.me/theorems/f7bafd4a-3fa3-429e-8ffc-dded1b63cfd4
-- title:
--   (109), §D.2, p. 54 — the argmax of the limit is the limit of the argmax
-- statement:
--   Let $m_n \in \mathbb R^K$, $n \in \mathbb N$, be a sequence of vectors that converges coordinatewise to a vector $v \in \mathbb R^K$ whose entries are pairwise distinct: $m_n(a) \to v(a)$ for every arm $a$, and $v(i) \ne v(j)$ for $i \ne j$. Let $\operatorname{sel}$ be any tie-breaking rule for $\operatorname{argmax}$, i.e. any map sending a vector $f$ to an arm $\operatorname{sel}(f)$ with $f(a) \le f(\operatorname{sel}(f))$ for all $a$. Then there is $n_0$ such that
--   $$\operatorname{sel}(m_n) = \operatorname{sel}(v) = \operatorname*{argmax}_a v(a) \qquad \text{for all } n \ge n_0.$$
--   In the words of (109), $\operatorname{argmax}_a \lim_n m_n(a) = \lim_n \operatorname{argmax}_a m_n(a)$, where the limit of a sequence of arms means that it is eventually constant.
--
--   Applied with $m_n(a) = \hat\mu_{a,n}(\tilde\omega)$ and $v(a) = \mu_a(\tilde\theta_a)$, together with Proposition 5 and the assumption of Proposition 1, this gives (109). It is the deterministic step that turns almost-sure convergence of the posterior means into almost-sure convergence of the IRS.FH action.
--
--   **Formalization Note.** This is the deterministic core of (109): the almost-sure statement follows from it pointwise. Arms are `Fin K` with $K \ge 1$.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 54, §D.2, (109)

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace InfoRelaxTS.Asymptotic

/-- Display (109), §D.2, p. 54, deterministic core: if `m n a → v a` for every arm and the limit
`v` has pairwise distinct entries, then every argmax tie-breaking rule eventually picks the
(unique) argmax of `v`. -/
theorem display_109 {K : ℕ} [NeZero K] (sel : (Fin K → ℝ) → Fin K) (hsel : Gap.IsArgmaxSel sel)
    (m : ℕ → Fin K → ℝ) (v : Fin K → ℝ) (hv : Function.Injective v)
    (hm : ∀ a, Tendsto (fun n => m n a) atTop (𝓝 (v a))) :
    ∀ᶠ n in atTop, sel (m n) = sel v := by sorry

end InfoRelaxTS.Asymptotic
