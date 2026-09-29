-- Prove2me | Theorems.Thm_LogRegretOCO_EWOO_telescoping_product
-- name    : LogRegretOCO.EWOO.telescoping_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:44:17.361962+00:00
-- url     : https://prove2.me/theorems/900527fe-0bf0-4525-ac90-607696ee7a7e
-- title:
--   Eq. (18): ∏_{τ≤t} h_τ(x_τ) ≥ ∫_P ∏_{τ≤t} h_τ dx / vol(P)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be nonempty, closed, bounded and convex with positive Lebesgue volume, let $\alpha > 0$, and let $f_1, f_2, \dots : \mathbb{R}^n \to \mathbb{R}$ be continuous on $P$ and $\alpha$-exp-concave on $P$. Write $h_\tau(x) = e^{-\alpha f_\tau(x)}$ and let $x_\tau$ be the points played by Exponentially Weighted Online Optimization. Then for every $t \ge 1$,
--
--   $$
--   \prod_{\tau=1}^{t} h_\tau(x_\tau) \;\ge\; \frac{\int_P \prod_{\tau=1}^{t} h_\tau(x)\, dx}{\int_P 1\, dx} \;=\; \frac{\int_P \prod_{\tau=1}^{t} h_\tau(x)\, dx}{\mathrm{vol}(P)}.
--   $$
--
--   This is the telescoping product of the per-round Jensen inequalities: the product of the algorithm's values of $h_\tau$ is at least the average over $P$ of the product of the $h_\tau$. Combined with a lower bound on that average near a minimizer of the cumulative cost, it yields Theorem 7.
--
--   **Formalization Note** $\mathrm{vol}(P)$ is the Lebesgue measure of $P$ converted to a real number; it is finite because $P$ is bounded. The statement is the conjunction of the inequality with denominator $\int_P 1\,dx$ and the identity $\int_P 1\,dx = \mathrm{vol}(P)$, as printed. Continuity of each $f_t$ on $P$ is the standing assumption of §2.2 weakened to what the argument uses.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 187, Eq. (18)

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- Eq. (18) (Hazan–Agarwal–Kale 2007, p. 187): for every `t ≥ 1`,
`∏_{τ=1}^t h_τ(x_τ) ≥ ∫_P ∏_{τ=1}^t h_τ(x) dx / ∫_P 1 dx`, and `∫_P 1 dx = vol(P)`,
where `h_τ(x) = exp(-α f_τ(x))` and `x_τ` is the EWOO point. -/
theorem telescoping_product (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∫ x in P, ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ x)) / (∫ _x in P, (1 : ℝ))
        ≤ ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      (∫ _x in P, (1 : ℝ)) = (volume P).toReal := by sorry

end LogRegretOCO.EWOO
