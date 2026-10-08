-- Prove2me | Theorems.Thm_MartOT_Card_lemma_3_2
-- name    : MartOT.Card.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:18:55.363208+00:00
-- url     : https://prove2.me/theorems/a5c52660-0123-4ccf-b189-51570e0dd47d
-- title:
--   Lemma 3.2, p. 19 — if uncountably many fibres Γ_a have ≥ k points, some (a, b₁<…<b_k) is approximated from the right and from the left
-- statement:
--   For $\Gamma\subseteq\mathbb R^2$ and $a\in\mathbb R$ write $\Gamma_a=\{y\in\mathbb R:(a,y)\in\Gamma\}$ for the fibre of $\Gamma$ over $a$.
--
--   Let $k$ be a positive integer and $\Gamma\subseteq\mathbb R^2$ any set such that uncountably many $a\in\mathbb R$ satisfy $|\Gamma_a|\ge k$. Then there exist $a\in\mathbb R$ and $b_1<\dots<b_k$ in $\Gamma_a$ such that for every $\varepsilon>0$:
--
--   1. there are $a'>a$ and $b'_1<\dots<b'_k$ in $\Gamma_{a'}$ with
--   $$\max\big(|a-a'|,|b_1-b'_1|,\dots,|b_k-b'_k|\big)<\varepsilon;$$
--   2. there are $a''<a$ and $b''_1<\dots<b''_k$ in $\Gamma_{a''}$ with
--   $$\max\big(|a-a''|,|b_1-b''_1|,\dots,|b_k-b''_k|\big)<\varepsilon .$$
--
--   The same $a$ and $b_1,\dots,b_k$ serve for every $\varepsilon$ and for both sides. Combined with the variational lemma (Lemma 1.11), this produces two nearby fibres of the optimality set on which a finite rerouting of mass can be tested; it is used for the cardinality bound of Theorem 7.1 with $k+1$ points.
--
--   **Formalization Note** $|\Gamma_a|$ is the cardinality in $\mathbb N\cup\{\infty\}$ (`Set.encard`), so infinite fibres count. The $k$-tuples are strictly increasing maps $\{0,\dots,k-1\}\to\mathbb R$, and the maximum being $<\varepsilon$ is written coordinatewise. No measurability of $\Gamma$ is assumed, as on the page.
-- source:
--   arXiv:1208.1509v2, Lemma 3.2, p. 19

import Mathlib

namespace MartOT.Card

theorem lemma_3_2 (k : ℕ) (hk : 0 < k) (Γ : Set (ℝ × ℝ))
    (hΓ : ¬ {a : ℝ | (k : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard}.Countable) :
    ∃ (a : ℝ) (b : Fin k → ℝ), StrictMono b ∧ (∀ i, (a, b i) ∈ Γ) ∧
      ∀ ε : ℝ, 0 < ε →
        (∃ a' : ℝ, a < a' ∧ ∃ b' : Fin k → ℝ, StrictMono b' ∧ (∀ i, (a', b' i) ∈ Γ) ∧
          |a - a'| < ε ∧ ∀ i, |b i - b' i| < ε) ∧
        (∃ a'' : ℝ, a'' < a ∧ ∃ b'' : Fin k → ℝ, StrictMono b'' ∧ (∀ i, (a'', b'' i) ∈ Γ) ∧
          |a - a''| < ε ∧ ∀ i, |b i - b'' i| < ε) := by sorry

end MartOT.Card
