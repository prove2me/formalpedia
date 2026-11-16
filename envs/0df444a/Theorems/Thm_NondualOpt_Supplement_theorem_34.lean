-- Prove2me | Theorems.Thm_NondualOpt_Supplement_theorem_34
-- name    : NondualOpt.Supplement.theorem_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:16:55.28929+00:00
-- url     : https://prove2.me/theorems/f284cc7b-98ad-4667-a52f-0d1da8c97ab2
-- title:
--   Theorem 34 — sfat lower bound for $L^d_{p,q^*}$
-- statement:
--   Let $L^d_{p,q^*}$, $\Lambda_{p,q^*}$, $\theta$, $\log_+$ and $Q(\alpha,d)$ be as in Theorem 8.
--
--   1. For every $1\le p,q\le\infty$ with $(p,q)\ne(\infty,\infty)$ there is a constant $c>0$ depending only on $p,q$ such that for every $d\ge1$ and every $0<\alpha\le2\Lambda_{p,q^*}$,
--   $$
--   \mathrm{sfat}_\alpha(L^d_{p,q^*})\ \ge\ c\,Q(\alpha,d).
--   $$
--   2. There is a universal constant $c>0$ such that for every $d\ge1$ and every $0<\alpha\le2$,
--   $$
--   \mathrm{sfat}_\alpha(L^d_{\infty,1})\ \ge\ c\,d\Big(1+\log_+\frac1\alpha\Big).
--   $$
--
--   This is the lower half of Theorem 8: binary search over the coordinates of an evaluation cube amplifies the classical fat-shattering lower bounds by a logarithmic factor in the sequential setting.
--
--   **Formalization Note** Values are compared in the extended nonnegative reals; the exponent expressions are those of the published Theorem 30.
--
--   Differences from the source:
--   - encoding: $\gtrsim_{p,q}$ and the endpoint $\gtrsim$ → a constant $c>0$ depending only on $(p,q)$ (universal at the endpoint), chosen before $d$ and $\alpha$; reason: the meaning of $\gtrsim_{p,q}$ in §2
--   - encoding: $d\in\mathbb N$ → $d\ge1$; reason: for $d=0$ the first part has no admissible $\alpha$ and the endpoint bound is $0\le\mathrm{sfat}$; nothing is excluded
--   - encoding: $\log_+$, $1/\infty$, $\max\{q,2\}$ → $\max(\log t,0)$, $1/\infty=0$, the real $\max(q,2)$ in the $p\ge q$ branch (where $q<\infty$); reason: Lean conventions; the expressions are those of the published Theorem 30
--   - encoding: $\mathrm{sfat}_\alpha\in\mathbb N\cup\{\infty\}$ compared with real bounds → comparison in extended nonnegative reals; reason: same instances
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Theorem 34, p.42

import Mathlib
import Definitions.Def_NondualOpt_theta
import Definitions.Def_NondualOpt_lpBall
import Definitions.Def_NondualOpt_dotPair
import Definitions.Def_NondualOpt_crossDuality
import Definitions.Def_NondualOpt_linClassLp
import Definitions.Def_NondualOpt_sfat

open scoped ENNReal

namespace NondualOpt.Supplement

/-- **Theorem 34 (sfat lower bound).** Let `1 ≤ p, q ≤ ∞`, `(p, q) ≠ (∞, ∞)`, and
`0 < α ≤ 2Λ_{p,q∗}`. With `θ = 1/p − (1/q − 1/2)₊`,
`sfat_α(L^d_{p,q∗}) ≳_{p,q} min{α^{−1/θ}, d(1 + log₊(1/(α d^θ)))}` if `p < q`, and
`sfat_α(L^d_{p,q∗}) ≳_{p,q} min{(d^{1/q−1/p}/α)^{max{q,2}}, d(1 + log₊(d^{1/q−1/p}/(α d^{1/max{q,2}})))}`
if `p ≥ q`. For `p = q = ∞` and `0 < α ≤ 2`, `sfat_α(L^d_{∞,1}) ≳ d(1 + log₊(1/α))`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Theorem 34, p.42.

**Formalization Note.** (i) `≳_{p,q}` is a constant `c > 0` depending only on `(p, q)` (with `qs`
the conjugate exponent `q∗`), chosen before `d` and `α`; the endpoint's `≳` is a universal
constant. (ii) `Λ_{p,q∗}` is the published `crossDuality` of `(B_p^d, B_{q∗}^d)`. (iii)
`log₊ t = max(log t, 0)`, `1/∞ = 0`; in the `p ≥ q` branch `q < ∞`, so `max{q, 2}` is the real
`max q.toReal 2` (the expressions of the published `NondualOpt.theorem_30`). (iv) `d ≥ 1`.
Values in `ℝ≥0∞`. -/
theorem theorem_34 :
    (∀ p q qs : ℝ≥0∞, 1 ≤ p → 1 ≤ q → ¬(p = ⊤ ∧ q = ⊤) → q⁻¹ + qs⁻¹ = 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d → ∀ α : ℝ, 0 < α →
        α ≤ 2 * crossDuality (dotPair d) (lpBall p d) (lpBall qs d) →
        ENNReal.ofReal (c *
          (if p < q then
            min (α ^ (-(theta p q)⁻¹))
              (d * (1 + max 0 (Real.log (1 / (α * (d : ℝ) ^ theta p q)))))
          else
            min (((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) / α) ^ max q.toReal 2)
              (d * (1 + max 0 (Real.log ((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) /
                (α * (d : ℝ) ^ (max q.toReal 2)⁻¹))))))) ≤
          (sfat (linClassLp p qs d) α : ℝ≥0∞)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d → ∀ α : ℝ, 0 < α → α ≤ 2 →
      ENNReal.ofReal (c * d * (1 + max 0 (Real.log (1 / α)))) ≤
        (sfat (linClassLp ⊤ 1 d) α : ℝ≥0∞)) := by sorry

end NondualOpt.Supplement
