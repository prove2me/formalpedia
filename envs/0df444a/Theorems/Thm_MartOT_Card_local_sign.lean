-- Prove2me | Theorems.Thm_MartOT_Card_local_sign
-- name    : MartOT.Card.local_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:18:56.87096+00:00
-- url     : https://prove2.me/theorems/c6f777c7-c4ec-496b-9a86-b03b62efeb0a
-- title:
--   Proof of Theorem 7.1, p. 39 — near (a, b_i) the difference of (17) and (18) is nonzero with the sign of D·(a′ − a)
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be twice continuously differentiable, let $a\in\mathbb R$ and $b_0<b_i<b_k$. For $\beta\in\mathbb R$ put $\lambda(\beta)=\frac{\beta-b_0}{b_k-b_0}$, so that $\beta=b_\lambda=(1-\lambda)b_0+\lambda b_k$, and for $a'\in\mathbb R$ consider the two quantities of the paper
--   $$(17)\quad h(b_\lambda-a)+\lambda h(b_k-a')+(1-\lambda)h(b_0-a'),$$
--   $$(18)\quad h(b_\lambda-a')+\lambda h(b_k-a)+(1-\lambda)h(b_0-a).$$
--   Assume that the chord defect at $b_i$,
--   $$D=h'(b_i-a)-\big[(1-\lambda(b_i))\,h'(b_0-a)+\lambda(b_i)\,h'(b_k-a)\big],$$
--   is nonzero. Then there is $\varepsilon_1>0$ such that whenever $|b_i-\beta|<\varepsilon_1$ and $0<|a-a'|<\varepsilon_1$, the difference $(17)-(18)$ is nonzero and has the sign of $D\,(a'-a)$:
--   $$\big[(17)-(18)\big]\cdot D\,(a'-a)>0 .$$
--   In particular, for $a'$ close to $a$ the sign of the difference is determined by the sign of $a-a'$. In the proof of Theorem 7.1, (17) is the cost of the competitor $\alpha'$ and (18) the cost of $\alpha$, so choosing $a'$ on the correct side of $a$ makes the competitor strictly cheaper.
--
--   **Formalization Note** The page's $\varepsilon_1<\varepsilon$, where $\varepsilon$ comes from the Taylor display just above it, is dropped: that display is not posed (it is false when $h''(b_i-a)=0$, e.g. $h(t)=t^3$ at $t=0$), and the claim here only needs $\varepsilon_1>0$. The sign is stated for $(17)-(18)$; the page's "(19)" is the first-order term of this difference.
-- source:
--   arXiv:1208.1509v2, §7.1, proof of Theorem 7.1, p. 39, displays (17), (18), (19) and the sentence "More precisely, as h″ is continuous …"

import Mathlib

namespace MartOT.Card

/-- Proof of Theorem 7.1, p. 39. For `β` near `b_i` put `λ = (β − b_0)/(b_k − b_0)`, so that
`β = b_λ = (1 − λ) b_0 + λ b_k`, and compare
(17) `h(b_λ − a) + λ h(b_k − a′) + (1 − λ) h(b_0 − a′)` with
(18) `h(b_λ − a′) + λ h(b_k − a) + (1 − λ) h(b_0 − a)`.
If the chord defect `D = h′(b_i − a) − [(1 − λ_i) h′(b_0 − a) + λ_i h′(b_k − a)]` at `b_i` is nonzero,
then for `β` and `a′` close enough to `b_i` and `a` (with `a′ ≠ a`), (17) − (18) is nonzero and has the
sign of `D · (a′ − a)`. -/
theorem local_sign (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (a b0 bk bi : ℝ)
    (h0i : b0 < bi) (hik : bi < bk)
    (hD : deriv h (bi - a) -
        ((1 - (bi - b0) / (bk - b0)) * deriv h (b0 - a) +
          (bi - b0) / (bk - b0) * deriv h (bk - a)) ≠ 0) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ β a' : ℝ, |bi - β| < ε₁ → 0 < |a - a'| → |a - a'| < ε₁ →
      0 < ((h (β - a) + (β - b0) / (bk - b0) * h (bk - a') +
              (1 - (β - b0) / (bk - b0)) * h (b0 - a')) -
            (h (β - a') + (β - b0) / (bk - b0) * h (bk - a) +
              (1 - (β - b0) / (bk - b0)) * h (b0 - a))) *
          ((deriv h (bi - a) -
              ((1 - (bi - b0) / (bk - b0)) * deriv h (b0 - a) +
                (bi - b0) / (bk - b0) * deriv h (bk - a))) * (a' - a)) := by sorry

end MartOT.Card
