-- Prove2me | Theorems.Thm_NondualOpt_Supplement_theorem_8
-- name    : NondualOpt.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:15:25.184729+00:00
-- url     : https://prove2.me/theorems/5128d77c-bed5-45c8-9fd0-f10ae2124a12
-- title:
--   Theorem 8 — near-optimal two-sided bounds on $\mathrm{sfat}_\alpha(L^d_{p,q^*})$
-- statement:
--   Let $1\le p,q\le\infty$, let $q^*$ be the conjugate exponent of $q$, let $L^d_{p,q^*}=\{B_{q^*}^d\ni g\mapsto\langle g,u\rangle:u\in B_p^d\}$, and let $\Lambda_{p,q^*}=\sup_{g\in B_{q^*}^d,u\in B_p^d}|\langle g,u\rangle|$. Write $\theta=\frac1p-\big(\frac1q-\frac12\big)_+$, $\log_+t=\max\{\log t,0\}$, $L_\alpha=1+\log_+(ed/\alpha)$, and
--   $$
--   Q(\alpha,d)=\begin{cases}\min\Big\{\alpha^{-1/\theta},\ d\Big(1+\log_+\dfrac{1}{\alpha d^{\theta}}\Big)\Big\}, & p<q,\\[2ex] \min\Big\{\Big(\dfrac{d^{1/q-1/p}}{\alpha}\Big)^{\max\{q,2\}},\ d\Big(1+\log_+\dfrac{d^{1/q-1/p}}{\alpha d^{1/\max\{q,2\}}}\Big)\Big\}, & p\ge q.\end{cases}
--   $$
--   There are constants $c,C>0$ depending only on $p,q$ such that for every $d\ge1$ and every $0<\alpha\le2\Lambda_{p,q^*}$:
--
--   1. if $(p,q)\ne(\infty,\infty)$, then $c\,Q(\alpha,d)\le\mathrm{sfat}_\alpha(L^d_{p,q^*})\le C\,L_\alpha\,Q(\alpha,d)$;
--   2. if $p=q=\infty$, then $c\,d\big(1+\log_+\frac1\alpha\big)\le\mathrm{sfat}_\alpha(L^d_{\infty,1})\le C\,d\big(1+\log_+\frac1\alpha\big)$.
--
--   These bounds determine the sequential fat-shattering dimension of the linear classes between $\ell_p$ and $\ell_{q^*}$ balls up to the factor $L_\alpha$, and feed the second part of Theorem 6.
--
--   **Formalization Note** Values are compared in the extended nonnegative reals; the exponent expressions are those of the published Theorem 30 (`NondualOpt.theorem_30`), which is the upper half.
--
--   Differences from the source:
--   - encoding: "up to constants depending only on $p,q$" → one pair $c,C>0$ for each $(p,q)$, chosen before $d$ and $\alpha$; reason: the meaning of $\lesssim_{p,q}$ in §2
--   - reading: at $p=q=\infty$ "we interpret its second line as $\mathrm{sfat}_\alpha(L^d_{\infty,1})\asymp d(1+\log_+(1/\alpha))$ on this same scale" → $c\,d(1+\log_+(1/\alpha))\le\mathrm{sfat}_\alpha(L^d_{\infty,1})\le C\,d(1+\log_+(1/\alpha))$ for $0<\alpha\le2\Lambda_{\infty,1}$, without the factor $L_\alpha$; reason: the sentence before the theorem replaces the undefined second line at $q=\infty$ by this two-sided bound
--   - encoding: $d\in\mathbb N$ → $d\ge1$; reason: for $d=0$ one has $\Lambda_{p,q^*}=0$ and no admissible $\alpha$, so nothing is excluded
--   - encoding: $\log_+$, $1/\infty$, $\max\{q,2\}$ → $\max(\log t,0)$, $1/\infty=0$, the real $\max(q,2)$ in the $p\ge q$ branch (where $q<\infty$); reason: Lean conventions; the expressions are those of the published Theorem 30
--   - encoding: $\mathrm{sfat}_\alpha\in\mathbb N\cup\{\infty\}$ compared with real bounds → comparison in extended nonnegative reals; reason: same instances; the upper bound excludes $\infty$
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Theorem 8, p.12 (L_α and the p = q = ∞ reading: §4.1, p.12)

import Mathlib
import Definitions.Def_NondualOpt_theta
import Definitions.Def_NondualOpt_lpBall
import Definitions.Def_NondualOpt_dotPair
import Definitions.Def_NondualOpt_crossDuality
import Definitions.Def_NondualOpt_linClassLp
import Definitions.Def_NondualOpt_sfat

open scoped ENNReal

namespace NondualOpt.Supplement

/-- **Theorem 8 (Near-optimal sfat bounds).** Let `1 ≤ p, q ≤ ∞` and `0 < α ≤ 2Λ_{p,q∗}`. With
`θ = 1/p − (1/q − 1/2)₊` and `L_α = 1 + log₊(ed/α)`, `sfat_α(L^d_{p,q∗})` lies, up to constants
depending only on `p, q`, between `Q` and `L_α · Q`, where
`Q = min{α^{−1/θ}, d(1 + log₊(1/(α d^θ)))}` if `p < q`, and
`Q = min{(d^{1/q−1/p}/α)^{max{q,2}}, d(1 + log₊(d^{1/q−1/p}/(α d^{1/max{q,2}})))}` if `p ≥ q`.
At `p = q = ∞` the second line is read as `sfat_α(L^d_{∞,1}) ≍ d(1 + log₊(1/α))` on the same
scale.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Theorem 8, p.12, with `L_α` and the
`p = q = ∞` reading from the paragraph before it (§4.1, p.12).

**Formalization Note.** (i) One pair of constants `c, C > 0` per `(p, q)` (with `qs` the conjugate
exponent `q∗`), chosen before `d` and `α`. (ii) `Λ_{p,q∗}` is the published `crossDuality` of
`(B_p^d, B_{q∗}^d)`; `L^d_{p,q∗}` is the published `linClassLp`. (iii) `log₊ t = max(log t, 0)`,
`1/∞ = 0`; in the `p ≥ q` branch with `(p, q) ≠ (∞, ∞)` one has `q < ∞`, so `max{q, 2}` is the
real `max q.toReal 2` (the expressions are those of the published `NondualOpt.theorem_30`).
(iv) At `p = q = ∞` the two-sided bound is `d(1 + log₊(1/α))` without `L_α`, as the paper's `≍`.
(v) `d ≥ 1` (for `d = 0`, `Λ = 0` and there is no admissible `α`). Values in `ℝ≥0∞`. -/
theorem theorem_8 :
    ∀ p q qs : ℝ≥0∞, 1 ≤ p → 1 ≤ q → q⁻¹ + qs⁻¹ = 1 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ α : ℝ, 0 < α →
        α ≤ 2 * crossDuality (dotPair d) (lpBall p d) (lpBall qs d) →
        (¬(p = ⊤ ∧ q = ⊤) →
          ENNReal.ofReal (c *
            (if p < q then
              min (α ^ (-(theta p q)⁻¹))
                (d * (1 + max 0 (Real.log (1 / (α * (d : ℝ) ^ theta p q)))))
            else
              min (((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) / α) ^ max q.toReal 2)
                (d * (1 + max 0 (Real.log ((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) /
                  (α * (d : ℝ) ^ (max q.toReal 2)⁻¹))))))) ≤
            (sfat (linClassLp p qs d) α : ℝ≥0∞) ∧
          (sfat (linClassLp p qs d) α : ℝ≥0∞) ≤ ENNReal.ofReal (C *
            (1 + max 0 (Real.log (Real.exp 1 * d / α))) *
            (if p < q then
              min (α ^ (-(theta p q)⁻¹))
                (d * (1 + max 0 (Real.log (1 / (α * (d : ℝ) ^ theta p q)))))
            else
              min (((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) / α) ^ max q.toReal 2)
                (d * (1 + max 0 (Real.log ((d : ℝ) ^ (q⁻¹.toReal - p⁻¹.toReal) /
                  (α * (d : ℝ) ^ (max q.toReal 2)⁻¹)))))))) ∧
        (p = ⊤ ∧ q = ⊤ →
          ENNReal.ofReal (c * d * (1 + max 0 (Real.log (1 / α)))) ≤
            (sfat (linClassLp p qs d) α : ℝ≥0∞) ∧
          (sfat (linClassLp p qs d) α : ℝ≥0∞) ≤
            ENNReal.ofReal (C * d * (1 + max 0 (Real.log (1 / α))))) := by sorry

end NondualOpt.Supplement
