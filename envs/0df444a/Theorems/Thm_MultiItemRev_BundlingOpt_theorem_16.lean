-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_theorem_16
-- name    : MultiItemRev.BundlingOpt.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:49.685665+00:00
-- url     : https://prove2.me/theorems/b5dcd1a7-189e-4de1-9808-2855e2298c67
-- title:
--   Theorem 16, p. 28 — under x f′(x) + (3/2) f(x) ≤ 0, bundling is optimal for two i.i.d. goods
-- statement:
--   Let $a > 0$ and let $F$ be a one-good distribution with values in $[a, \infty)$ whose density $f$ is differentiable and satisfies
--   $$x f'(x) + \tfrac32 f(x) \le 0 \qquad \text{for every } x > a. \tag{9}$$
--   Then bundling is optimal for two i.i.d.-$F$ goods $X_1, X_2$:
--   $$\mathrm{Rev}(X_1, X_2) = \mathrm{BRev}(X_1, X_2) = \mathrm{Rev}(X_1 + X_2).$$
--
--   Condition (9) says that $x^{3/2} f(x)$ is nonincreasing on $(a,\infty)$; it holds for $f(x) = c x^{-\gamma}$ with $\gamma \ge 3/2$, in particular for the equal-revenue distribution and for Pareto distributions with index $\alpha \ge 1/2$. The theorem identifies a class of distributions for which the optimal two-good mechanism is the simple bundled one, in contrast with the general multi-good setting where bundling can lose a constant or larger fraction of the optimal revenue.
--
--   **Formalization Note** The law $F$ is the pushforward to $\mathbb{R}_{\ge0}$ of $f\,dx$; continuity of $F$ is automatic for a law with a density and is not assumed separately. "Density function" is encoded as: $f$ measurable, $f \ge 0$, $\int f = 1$, and $f = 0$ on $(-\infty, a)$. Differentiability is required at every $x > a$, the range in which (9) is imposed; nothing is assumed about $f$ at $a$. Revenues take values in $[0,\infty]$ and may be infinite.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 28, Theorem 16 and (9); proof in Appendix A.6, pp. 44–46

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem theorem_16 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_supp : ∀ x, x < a → f x = 0)
    (hf_mass : ∫⁻ x, ENNReal.ofReal (f x) = 1)
    (hf_diff : ∀ x, a < x → DifferentiableAt ℝ f x)
    (h9 : ∀ x, a < x → x * deriv f x + 3 / 2 * f x ≤ 0) :
    Rev (Measure.pi (fun _ : Fin 2 => densityLaw f)) =
        BRev (Measure.pi (fun _ : Fin 2 => densityLaw f)) ∧
      BRev (Measure.pi (fun _ : Fin 2 => densityLaw f)) =
        Rev1 ((Measure.pi (fun _ : Fin 2 => densityLaw f)).map (fun x => x 0 + x 1)) := by sorry

end MultiItemRev.BundlingOpt
