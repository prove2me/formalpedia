-- Prove2me | Theorems.Thm_GaussMixHH_lemma_13
-- name    : GaussMixHH.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:31.007217+00:00
-- url     : https://prove2.me/theorems/22f906a9-00e1-4228-8d15-79f81635ba6f
-- title:
--   Lemma 13, p.20 — propagating $|G(-T)|\ge\beta$ into the observation disk $B$
-- statement:
--   There are universal constants $c,C,\alpha_0>0$ such that the following holds. Let $G$ be holomorphic on the open left half-plane and continuous on the closed left half-plane, with $|G(s)|\le2$ there. Let $n\in\mathbb N$, $T\ge1$, $0<\beta\le1$ with $|G(-T)|\ge\beta$, and $L=\log(2/\beta)$. For every $0<\alpha<\alpha_0$ there is $a\in B=\{|s+\tfrac14|<\tfrac14\}$ with
--
--   $$\big|(1+2a)^{n/2}G(a)\big|\ge\exp\Big(-C\frac{TL}{\alpha}-Cn\alpha^2\Big),$$
--
--   and moreover
--
--   1. $c\alpha^2\le\operatorname{dist}(a,\partial B)\le C\alpha^2$;
--   2. $c\alpha^2\le-\operatorname{Re}(a)\le C\alpha^2$;
--   3. $|\operatorname{Im}(a)|\le C\alpha$.
--
--   This moves a lower bound known at $-T$, far outside $B$, to a point of $B$ close to $0$, at a cost $TL/\alpha$ from Jensen's formula and $n\alpha^2$ from the Gaussian factor.
--
--   **Formalization Note** $(1+2a)^{n/2}$ is the principal power; the universal constants and the threshold for "sufficiently small $\alpha$" are chosen before $G$, $n$, $T$, $\beta$.
--
--   Differences from the source:
--   - encoding: universal c, C and "for every sufficiently small α > 0" → ∃ c C α₀ > 0 before G, n, T, β, then ∀ α ∈ (0, α₀); reason: the convention of p.19; the proof's smallness threshold is absolute (7α²/16 − 4α⁴ > 0, 1 − 4α² ≥ e^{−Cα²})
--   - encoding: −Re(a) = Θ(α²); dist(a, ∂B) → cα² ≤ −Re a ≤ Cα²; Metric.infDist a (sphere (−1/4) (1/4)); reason: the meaning of Θ; ∂B is that circle
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 13, p.20 (PDF p.22); B defined p.19

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform

open Complex Metric

namespace GaussMixHH

/-- **Lemma 13** (Propagating `|G(−T)| ≥ β` into `B`).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 13, p.20 (PDF p.22); `B` is
defined on p.19.

"Let G be holomorphic on the open left half-plane and continuous on the closed left half-plane,
with |G(s)| ≤ 2 there. Suppose T ≥ 1, 0 < β ≤ 1, and |G(−T)| ≥ β, and put L = log(2/β). For every
sufficiently small α > 0, there is a ∈ B such that |(1 + 2a)^{n/2}G(a)| ≥ exp(−C TL/α − Cnα²), and
additionally, cα² ≤ dist(a, ∂B) ≤ Cα², −Re(a) = Θ(α²), |Im(a)| ≤ Cα."

**Formalization Note.**
* "c, C > 0 denote universal constants" (p.19): `c, C` and the threshold `α₀` of "sufficiently
  small" are chosen before `G, n, T, β, α`. One `C` serves every upper bound.
* `B = obsDisk = ball(−1/4, 1/4)`, `∂B = sphere(−1/4, 1/4)`, and `dist(a, ∂B)` is
  `Metric.infDist a ∂B`. `−Re(a) = Θ(α²)` is `cα² ≤ −Re a ≤ Cα²`.
* `(1 + 2a)^{n/2}` is `Complex.cpow` (principal branch); `n` is any natural number.
* `G` is any function with the stated properties, not only `G_ν`. -/
theorem lemma_13 :
    ∃ c C α₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < α₀ ∧
      ∀ (G : ℂ → ℂ) (n : ℕ) (T β : ℝ),
        DifferentiableOn ℂ G {s : ℂ | s.re < 0} → ContinuousOn G {s : ℂ | s.re ≤ 0} →
        (∀ s : ℂ, s.re ≤ 0 → ‖G s‖ ≤ 2) → 1 ≤ T → 0 < β → β ≤ 1 → β ≤ ‖G (-(T : ℂ))‖ →
        ∀ α : ℝ, 0 < α → α < α₀ →
          let L := Real.log (2 / β)
          ∃ a ∈ obsDisk,
            Real.exp (-(C * T * L / α) - C * n * α ^ 2) ≤ ‖(1 + 2 * a) ^ ((n : ℂ) / 2) * G a‖ ∧
            c * α ^ 2 ≤ infDist a (sphere (-1 / 4 : ℂ) (1 / 4)) ∧
            infDist a (sphere (-1 / 4 : ℂ) (1 / 4)) ≤ C * α ^ 2 ∧
            c * α ^ 2 ≤ -a.re ∧ -a.re ≤ C * α ^ 2 ∧ |a.im| ≤ C * α := by sorry

end GaussMixHH
