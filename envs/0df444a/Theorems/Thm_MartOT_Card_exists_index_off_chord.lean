-- Prove2me | Theorems.Thm_MartOT_Card_exists_index_off_chord
-- name    : MartOT.Card.exists_index_off_chord
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:22.234981+00:00
-- url     : https://prove2.me/theorems/4bec1e48-2b4d-4022-affb-96316ca70749
-- title:
--   Proof of Theorem 7.1, p. 39 — if lines meet h′ in ≤ k points, some interior b_i of b₀<…<b_k makes (19) nonzero
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ and $k\in\mathbb N$, and assume that every affine function $x\mapsto sx+t$ meets $h'$ in at most $k$ points: $|\{x: h'(x)=sx+t\}|\le k$ for all $s,t\in\mathbb R$. Let $a\in\mathbb R$ and $b_0<b_1<\dots<b_k$. For an index $i$ let $\lambda_i=\frac{b_i-b_0}{b_k-b_0}$, so that $b_i=(1-\lambda_i)b_0+\lambda_i b_k$.
--
--   Then there is an index $i\in\{1,\dots,k-1\}$ such that for every $a'\ne a$ the quantity (19) of the paper is nonzero:
--   $$\Big(h'(b_i-a)-\big[(1-\lambda_i)\,h'(b_0-a)+\lambda_i\,h'(b_k-a)\big]\Big)(a'-a)\neq0 .$$
--
--   In words: the $k+1$ points $(b_j-a,\,h'(b_j-a))$ cannot all lie on the chord through the two extreme ones, because that chord would meet $h'$ in $k+1$ points. This is the step of the proof of Theorem 7.1 where the hypothesis on $h'$ enters.
--
--   **Formalization Note** The page's $b_\lambda=b_i$ is encoded by taking $\lambda=\lambda_i$. The index $i$ is chosen before $a'$. Here $h'$ is Lean's `deriv h`; no differentiability of $h$ is assumed, which only makes the statement more general. For $k\le1$ the hypothesis is satisfied by no function at all (the line through two points of the graph of $h'$ meets it twice), so the statement says nothing there; no hypothesis $k\ge2$ is added.
-- source:
--   arXiv:1208.1509v2, §7.1, proof of Theorem 7.1, p. 39, paragraph after the error estimate (display (19))

import Mathlib

namespace MartOT.Card

/-- Proof of Theorem 7.1, p. 39: with `λ = (b_i − b_0)/(b_k − b_0)`, so that
`b_i = (1 − λ) b_0 + λ b_k`, the quantity (19)
`(h′(b_i − a) − [(1 − λ) h′(b_0 − a) + λ h′(b_k − a)]) (a′ − a)` is nonzero for some interior index
`i ∈ {1, …, k − 1}` and every `a′ ≠ a`. -/
theorem exists_index_off_chord (h : ℝ → ℝ) (k : ℕ)
    (hk : ∀ s t : ℝ, {x : ℝ | deriv h x = s * x + t}.encard ≤ k)
    (a : ℝ) (b : Fin (k + 1) → ℝ) (hb : StrictMono b) :
    ∃ i : Fin (k + 1), 0 < (i : ℕ) ∧ (i : ℕ) < k ∧
      ∀ a' : ℝ, a' ≠ a →
        (deriv h (b i - a) -
            ((1 - (b i - b 0) / (b (Fin.last k) - b 0)) * deriv h (b 0 - a) +
              (b i - b 0) / (b (Fin.last k) - b 0) * deriv h (b (Fin.last k) - a))) *
          (a' - a) ≠ 0 := by sorry

end MartOT.Card
