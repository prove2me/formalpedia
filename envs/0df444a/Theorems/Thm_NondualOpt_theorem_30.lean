-- Prove2me | Theorems.Thm_NondualOpt_theorem_30
-- name    : NondualOpt.theorem_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:39.082618+00:00
-- url     : https://prove2.me/theorems/f67df107-0102-441a-a69e-d3aed73db85c
-- title:
--   Theorem 30 — sfat upper bound for $L^d_{p,q^*}$
-- statement:
--   Let $\theta=\frac1p-(\frac1q-\frac12)_+$ and $L_\alpha=1+\log_+(ed/\alpha)$. For every $1\le p,q\le\infty$ with $(p,q)\ne(\infty,\infty)$, every $d\ge1$ and every $\alpha>0$,
--   $$
--   \mathrm{sfat}_\alpha(L^d_{p,q^*})\lesssim_{p,q}L_\alpha\cdot\begin{cases}\min\Big\{\alpha^{-1/\theta},\ d\Big(1+\log_+\frac1{\alpha d^{\theta}}\Big)\Big\},&p<q,\\[1ex]\min\Big\{\Big(\frac{d^{1/q-1/p}}\alpha\Big)^{\max\{q,2\}},\ d\Big(1+\log_+\frac{d^{1/q-1/p}}{\alpha d^{1/\max\{q,2\}}}\Big)\Big\},&p\ge q,\end{cases}
--   $$
--   and at $p=q=\infty$, $\mathrm{sfat}_\alpha(L^d_{\infty,1})\lesssim d(1+\log_+(1/\alpha))$. With Theorem 6 this yields the rate $\tilde O_{p,q}(T^{-\theta})$ of Corollary 7.
--
--   Differences from the source:
--   - encoding: ≲_{p,q} and ≲ → a constant depending only on (p, q) (with q∗ as an argument) chosen before d and α; a universal constant at p = q = ∞; reason: definition of ≲
--   - encoding: the case split p < q / p ≥ q with max{q, 2}; d ∈ ℕ → if p < q then … else …, with max{q, 2} = max(q, 2) as a real (q < ∞ in the p ≥ q branch since (p, q) ≠ (∞, ∞)); d ≥ 1; values in [0, ∞]; reason: same statement
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Theorem 30, p.40 (L_α: §4.1, p.12, and p.37)

import Mathlib
import Definitions.Def_NondualOpt_theta
import Definitions.Def_NondualOpt_linClassLp
import Definitions.Def_NondualOpt_sfat

open scoped ENNReal

namespace NondualOpt

/-- **Theorem 30 (sfat upper bound).** For every `1 ≤ p, q ≤ ∞` with `(p, q) ≠ (∞, ∞)` and `α > 0`,
with `θ = 1/p − (1/q − 1/2)₊` and `L_α = 1 + log₊(ed/α)`,
`sfat_α(L^d_{p,q∗}) ≲_{p,q} L_α · min{α^{−1/θ}, d(1 + log₊(1/(α d^θ)))}` if `p < q`, and
`sfat_α(L^d_{p,q∗}) ≲_{p,q} L_α · min{(d^{1/q−1/p}/α)^{max{q,2}}, d(1 + log₊(d^{1/q−1/p}/(α d^{1/max{q,2}})))}`
if `p ≥ q`. At `p = q = ∞`, `sfat_α(L^d_{∞,1}) ≲ d(1 + log₊(1/α))`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Theorem 30, p.40 (`L_α` defined in §4.1,
p.12, and before (21), p.37).

**Formalization Note.** `≲_{p,q}` is a constant depending only on `(p, q)` (with `q∗` the
conjugate exponent `qs`), chosen before `d` and `α`; the endpoint constant is universal.
`log₊ t = max(log t, 0)`, `1/∞ = 0`; in the `p ≥ q` branch `q < ∞`, so `max{q, 2}` is the real
`max q.toReal 2`. `d ≥ 1`. Values in `ℝ≥0∞`. -/
theorem theorem_30 :
    (∀ p q qs : ℝ≥0∞, 1 ≤ p → 1 ≤ q → ¬(p = ⊤ ∧ q = ⊤) → q⁻¹ + qs⁻¹ = 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ α : ℝ, 0 < α →
        (sfat (linClassLp p qs d) α : ℝ≥0∞) ≤ ENNReal.ofReal (C *
          (1 + max 0 (Real.log (Real.exp 1 * d / α))) *
          (if p < q then
            min (α ^ (-(theta p q)⁻¹))
              (d * (1 + max 0 (Real.log (1 / (α * (d : ℝ) ^ theta p q)))))
          else
            min (((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) / α) ^ max q.toReal 2)
              (d * (1 + max 0 (Real.log ((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) /
                (α * (d : ℝ) ^ (max q.toReal 2)⁻¹)))))))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ α : ℝ, 0 < α →
      (sfat (linClassLp ⊤ 1 d) α : ℝ≥0∞) ≤
        ENNReal.ofReal (C * d * (1 + max 0 (Real.log (1 / α))))) := by sorry

end NondualOpt
