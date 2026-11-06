-- Prove2me | Theorems.Thm_OAI_Falconer_linear_projection_gain
-- name    : OAI.Falconer.linear_projection_gain
-- status  : Proved
-- author  : @dangnguyen
-- created : 2026-11-05T19:30:11.18091+00:00
-- url     : https://prove2.me/theorems/f43a8903-3260-48b5-a77a-2baa54feae93
-- title:
--   Linear projection gain for tube incidences (Falconer, Theorem 4.1)
-- statement:
--   Fix an integer $k\ge 2$ and exponents with $k-1\le q\le k-\tfrac12<t<k$. Fix a tube-width constant $C\ge 0$, a support radius $R\ge 0$, and, when $q=k-1$, a plate exponent $\zeta>0$. Then there are $\varepsilon>0$, $c>0$ and $\delta_0>0$ such that the following holds for every $0<\delta<\delta_0$.
--
--   Let $\mu$ be a Borel measure on $\mathbb R^{k+1}$ of total mass at most $1$, carried by the ball $|x|\le R$, and let $\nu$ be a Borel measure on the unit sphere $S^k$ of total mass at most $1$. Suppose that for all $\delta\le r\le 1$
--   $$\mu(B(x,r))\le \delta^{-\varepsilon}r^{t}\quad(x\in\mathbb R^{k+1}),\qquad \nu(B(w,r))\le \delta^{-\varepsilon}r^{q}\quad(w\in S^k),$$
--   and, in the endpoint case $q=k-1$, also $\nu\{w:\operatorname{dist}(w,H)\le r\}\le \delta^{-\varepsilon}r^{\zeta}$ for every linear hyperplane $H$.
--
--   Let $E\subset\mathbb R^{k+1}\times S^k$ be measurable for the completed product measure, with fibers $E_w=\{x:(x,w)\in E\}$. Suppose that for every direction $w$ there is a set $A_w$ of at most $\delta^{-q-\varepsilon}$ points such that every $x\in E_w$ lies within distance $C\delta$ of a line $a+\mathbb Rw$ with $a\in A_w$. In other words, each fiber is covered by at most $\delta^{-q-\varepsilon}$ tubes of width $C\delta$ parallel to $w$. Then
--   $$(\mu\otimes\nu)(E)\le \delta^{c}.$$
--
--   The constants depend only on $k,q,t,C,R,\zeta$. They are uniform over all measures and incidence relations satisfying these bounds. The paper takes the tubes to have bounded length. Since $\mu$ lives in a fixed ball, this makes no difference to the incidence mass, so the statement uses full tubes.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 4.1, Theorem 4.1 (Linear projection gain), label ang:linear-gain, with the conventions of Section 2.

import Mathlib

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace OAI.Falconer

theorem linear_projection_gain
    (k : ℕ) (hk : 2 ≤ k) (q t : ℝ)
    (hq : (k : ℝ) - 1 ≤ q) (hq' : q ≤ (k : ℝ) - 1 / 2)
    (ht : (k : ℝ) - 1 / 2 < t) (ht' : t < (k : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (R : ℝ) (hR : 0 ≤ R)
    (ζ : ℝ) (hζ : q = (k : ℝ) - 1 → 0 < ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        (ν : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)),
      μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ᵐ x ∂μ, ‖x‖ ≤ R) →
      (∀ x : EuclideanSpace ℝ (Fin (k + 1)), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ t)) →
      (∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
        ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν (Metric.ball w r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ q)) →
      (q = (k : ℝ) - 1 →
        ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 1))),
        Module.finrank ℝ H = k → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν {w | Metric.infDist (w : EuclideanSpace ℝ (Fin (k + 1))) (H : Set _) ≤ r}
          ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ ζ)) →
      ∀ E : Set (EuclideanSpace ℝ (Fin (k + 1)) ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1),
      NullMeasurableSet E (μ.prod ν) →
      (∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
        ∃ A : Finset (EuclideanSpace ℝ (Fin (k + 1))),
          (A.card : ℝ) ≤ δ ^ (-q - ε) ∧
          ∀ x : EuclideanSpace ℝ (Fin (k + 1)), (x, w) ∈ E →
            ∃ a ∈ A,
              ‖(ℝ ∙ (w : EuclideanSpace ℝ (Fin (k + 1))))ᗮ.orthogonalProjectionOnto
                (x - a)‖ ≤ C * δ) →
      (μ.prod ν) E ≤ ENNReal.ofReal (δ ^ c) := by sorry

end OAI.Falconer
