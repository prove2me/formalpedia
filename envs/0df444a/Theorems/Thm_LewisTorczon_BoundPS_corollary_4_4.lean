-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_corollary_4_4
-- name    : LewisTorczon.BoundPS.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:47:31.723541+00:00
-- url     : https://prove2.me/theorems/a15e305a-d5e7-4881-afd1-e189f3797cb7
-- title:
--   Corollary 4.4 — if $\liminf\|q(x_k)\|\ne0$ then $\Delta_k$ is bounded away from zero
-- statement:
--   Let $x_k,\Delta_k$ be a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):x\in\Omega\}$. Suppose that $L_\Omega(x_0)$ is compact, that $f$ is continuously differentiable on an open set containing $\Omega$, and that
--   $$\liminf_{k\to\infty}\|q(x_k)\|\ne0 .$$
--   Then there is a constant $\Delta_*>0$ such that $\Delta_k>\Delta_*$ for all $k$.
--
--   The corollary is one half of the contradiction proving Theorem 3.2; Theorem 4.5 is the other.
--
--   **Formalization Note** For the nonnegative sequence $\|q(x_k)\|$, "$\liminf\ne0$" is encoded as: it is not the case that for every $\varepsilon>0$ one has $\|q(x_k)\|<\varepsilon$ for infinitely many $k$ (no `Filter.liminf`, which is not meaningful for unbounded sequences in Lean). The smoothness hypothesis is taken on an open set $U\supseteq\Omega$.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 10, Corollary 4.4

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Corollary 4.4**, p. 10: if `L_Ω(x_0)` is compact, `f` is `C¹` and
`liminf_{k→∞} ‖q(x_k)‖ ≠ 0` (encoded as: it is not the case that `‖q(x_k)‖ < ε` infinitely often
for every `ε > 0`), then there is `Δ_* > 0` with `Δ_k > Δ_*` for all `k`. -/
theorem corollary_4_4 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hliminf : ¬ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ‖projQ lo hi f (R.x k)‖ < ε) :
    ∃ Δstar : ℝ, 0 < Δstar ∧ ∀ k, Δstar < R.Δ k := by sorry

end LewisTorczon.BoundPS
