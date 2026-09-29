-- Prove2me | Theorems.Thm_LogRegretOCO_EWOO_product_lower_bound
-- name    : LogRegretOCO.EWOO.product_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:46:19.311978+00:00
-- url     : https://prove2.me/theorems/5851902e-9d4b-4020-9e6b-289293091f4d
-- title:
--   §3.4 (p. 187): ∏ h_τ(x_τ) ≥ vol(S)/vol(P)·(1/e)∏ h_τ(x*) ≥ ∏ h_τ(x*)/(e(T+1)^n)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be nonempty, closed, bounded and convex with positive Lebesgue volume, let $\alpha > 0$, and let $f_1, f_2, \dots : \mathbb{R}^n \to \mathbb{R}$ be continuous on $P$ and $\alpha$-exp-concave on $P$. Write $h_\tau(x) = e^{-\alpha f_\tau(x)}$, let $x_\tau$ be the points played by Exponentially Weighted Online Optimization, fix $T \ge 1$ and a comparator $x^* \in P$, and let $S = \{\frac{T}{T+1}x^* + \frac{1}{T+1}y : y \in P\}$. Then
--
--   $$
--   \prod_{\tau=1}^{T} h_\tau(x_\tau) \;\ge\; \frac{\mathrm{vol}(S)}{\mathrm{vol}(P)} \cdot \frac{1}{e} \prod_{\tau=1}^{T} h_\tau(x^*) \;\ge\; \frac{1}{e\,(T+1)^n} \prod_{\tau=1}^{T} h_\tau(x^*).
--   $$
--
--   This is the multiplicative form of the EWOO regret bound: taking logarithms turns it into $\sum_{\tau=1}^T (f_\tau(x_\tau) - f_\tau(x^*)) \le \frac{1}{\alpha}(1 + n\log(T+1))$, from which Theorem 7 follows.
--
--   **Formalization Note** The paper takes $x^*$ to be a minimizer of $\sum_{t=1}^T f_t$ over $P$; the inequality is stated for every $x^* \in P$, which is equivalent for the regret and avoids naming a minimizer. Volumes are converted to real numbers (both are finite and $\mathrm{vol}(P) > 0$). Continuity of each $f_t$ on $P$ is the standing assumption of §2.2 weakened to what the argument uses.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 187, §3.4, proof of Theorem 7, last display on p. 187

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- §3.4, last display on p. 187 (Hazan–Agarwal–Kale 2007): for every comparator `x* ∈ P`,
`∏_{τ=1}^T h_τ(x_τ) ≥ vol(S)/vol(P) · (1/e) ∏_{τ=1}^T h_τ(x*) ≥ 1/(e(T+1)^n) ∏_{τ=1}^T h_τ(x*)`,
where `h_τ = exp(-α f_τ)`, `x_τ` is the EWOO point and `S` the shrunken set around `x*`. -/
theorem product_lower_bound (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (T : ℕ) (hT : 1 ≤ T) (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ P) :
    (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) *
          ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
        ≤ ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      1 / (Real.exp 1 * ((T : ℝ) + 1) ^ n) * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
        ≤ (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) *
          ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar) := by sorry

end LogRegretOCO.EWOO
