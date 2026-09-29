-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_ftl_regret_bound
-- name    : LogRegretOCO.FTAL.ftl_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:41:26.831595+00:00
-- url     : https://prove2.me/theorems/4e23ed82-55b9-4935-b244-cc2fca63c136
-- title:
--   Theorem 5 (corrected constant) — Follow the Leader on costs $g_t(v_t^\top x)$ has logarithmic regret
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be nonempty, convex, closed and bounded, with $\|y - z\| \le D$ for all $y, z \in P$. For each round $t \ge 1$ let the cost be $f_t(x) = g_t(v_t^\top x)$, where $v_t \in \mathbb{R}^n$ and $g_t : \mathbb{R} \to \mathbb{R}$ is convex. Assume there are $R, a, b > 0$ such that for all $t \ge 1$:
--
--   1. $\|v_t\|_2 \le R$;
--   2. for every $x \in P$, $g_t$ is twice differentiable at $v_t^\top x$ (precisely: $g_t$ and $g_t'$ are differentiable there), with $|g_t'(v_t^\top x)| \le b$ and $g_t''(v_t^\top x) \ge a$.
--
--   Let $x_1, x_2, \dots$ be a run of Follow the Leader on $f$ over $P$. Then for every $T \ge 1$ and every $u \in P$,
--
--   $$
--   \sum_{t=1}^T \bigl(f_t(x_t) - f_t(u)\bigr) \le \frac{n b^2}{a} \log\left(\frac{a^2 D^2 R^2 T^2}{b^2} + 1\right) + \frac{b^2}{a}.
--   $$
--
--   The theorem shows that plain Follow the Leader already achieves $O(\log T)$ regret when each cost is a strongly curved convex function of a single linear form, a class that contains the quadratic surrogates of Follow the Approximate Leader and the losses of portfolio selection.
--
--   **Formalization Note** The paper prints the bound $\frac{2nb^2}{a}\bigl[\log\frac{DRaT}{b} + 1\bigr]$. That is false when $DRaT/b < 1/e$, where it is negative (for $n = 1$, $P = [0,1]$, $v_t = 1$, $g_t(y) = y^2/20$, $b = 1$, $T = 1$, $x_1 = 1$ the regret is $1/20 > 0$). The paper's proof (Claims 1 and 2 with $\varepsilon = b^2/(aD^2T)$) gives the displayed bound, which implies the printed one when $DRaT \ge b$; the displayed form is stated because Theorem 6 applies Theorem 5 with $DRa/b \le 1/16$. The paper writes "$f_t : P \to \mathbb{R}^n$", a typo for $\mathbb{R}$. Derivatives are Mathlib's `deriv`, with explicit differentiability hypotheses at the points $v_t^\top x$, $x \in P$ (where `deriv` would otherwise return the junk value $0$). Rounds are $1$-based; regret is stated against every comparator $u \in P$ rather than with a real-valued $\min$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 182, Theorem 5 (proof pp. 183–185, Claims 1–2 and the display on p. 185)

import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL
theorem ftl_regret_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (D R a b : ℝ)
    (g : ℕ → ℝ → ℝ) (v : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPclosed : IsClosed P)
    (hPbdd : Bornology.IsBounded P)
    (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hv : ∀ t, 1 ≤ t → ‖v t‖ ≤ R)
    (hgconv : ∀ t, 1 ≤ t → ConvexOn ℝ Set.univ (g t))
    (hgdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (g t) (inner ℝ (v t) y))
    (hgdiff2 : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (deriv (g t)) (inner ℝ (v t) y))
    (hg1 : ∀ t, 1 ≤ t → ∀ y ∈ P, |deriv (g t) (inner ℝ (v t) y)| ≤ b)
    (hg2 : ∀ t, 1 ≤ t → ∀ y ∈ P, a ≤ deriv (deriv (g t)) (inner ℝ (v t) y))
    (hx : IsFTLRun P (fun t y => g t (inner ℝ (v t) y)) x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (g t (inner ℝ (v t) (x t)) - g t (inner ℝ (v t) u))
        ≤ n * b ^ 2 / a * Real.log (a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 + 1)
          + b ^ 2 / a := by sorry
end LogRegretOCO.FTAL
