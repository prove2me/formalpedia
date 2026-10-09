-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_revenue_le_majorant
-- name    : MultiItemRev.BundlingOpt.revenue_le_majorant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:26:04.745185+00:00
-- url     : https://prove2.me/theorems/f80f1add-80f9-4fa0-a744-4e63b3f43172
-- title:
--   Proof of Theorem 16, pp. 45–46 — under (9), R(µ; X) ≤ R(µ̂; X) for symmetric IC, IR, NPT µ
-- statement:
--   Let $a > 0$ and let $f$ be a probability density on $\mathbb{R}$ that vanishes on $(-\infty, a)$, is differentiable at every $x > a$, and satisfies
--   $$x f'(x) + \tfrac32 f(x) \le 0 \qquad \text{for every } x > a. \tag{9}$$
--   Let $X = (Y, Z)$ with $Y, Z$ i.i.d. with density $f$. Then for every admissible, NPT and symmetric two-good mechanism $\mu$, its bundled majorant $\hat\mu$ at level $a$ yields at least as much revenue:
--   $$R(\mu; X) \ \le\ R(\hat\mu; X).$$
--
--   This is where condition (9) enters the proof of Theorem 16: it makes the coefficients of $b$ in the integrated-by-parts revenue formula nonnegative, so that replacing $b$ by the larger $\hat b$ of (18) can only increase revenue.
--
--   **Formalization Note** Revenues are extended reals and may be $+\infty$. Measurability of $f$ is part of "density function". Differentiability is required at every $x > a$, the range of (9); nothing is assumed about $f$ at $a$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 45–46, proof of Theorem 16 (r_M(b) ≤ r_M(b̂); R(µ;X) ≤ R(µ̂;X))

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem revenue_le_majorant (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_supp : ∀ x, x < a → f x = 0)
    (hf_mass : ∫⁻ x, ENNReal.ofReal (f x) = 1)
    (hf_diff : ∀ x, a < x → DifferentiableAt ℝ f x)
    (h9 : ∀ x, a < x → x * deriv f x + 3 / 2 * f x ≤ 0)
    (M : Mechanism (Fin 2)) (hM : IsAdmissible M ∧ IsNPT M) (hsym : IsSymmetric M) :
    expRevenue (Measure.pi (fun _ : Fin 2 => densityLaw f)) M ≤
      expRevenue (Measure.pi (fun _ : Fin 2 => densityLaw f)) (bundledMajorant M a.toNNReal) := by sorry

end MultiItemRev.BundlingOpt
