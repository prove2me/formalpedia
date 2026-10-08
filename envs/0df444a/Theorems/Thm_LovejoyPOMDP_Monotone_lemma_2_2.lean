-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_2_2
-- name    : LovejoyPOMDP.Monotone.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:39:38.857375+00:00
-- url     : https://prove2.me/theorems/b4e98ea7-6257-42d8-8690-feea716d58a3
-- title:
--   Lemma 2.2 — dominated increments order the maximizer sets on a finite chain
-- statement:
--   Let $A$ be a finite, nonempty, completely ordered set and let $f,f':A\to\mathbb R$. Let $A^*$ and $A'^*$ be the sets of maximizers of $f$ and $f'$ on $A$. Suppose that for every $a\ge a'$ in $A$,
--   $$f(a)-f(a')\ \ge\ f'(a)-f'(a').$$
--   Then
--
--   1. for every $a^*\in A^*$ there is an $a'^*\in A'^*$ with $a'^*\le a^*$, and
--   2. for every $a'^*\in A'^*$ there is an $a^*\in A^*$ with $a^*\ge a'^*$.
--
--   If $f$ grows faster than $f'$ along the chain, then the maximizers of $f$ lie above those of $f'$ in both senses. Proposition 2 applies this to $f=h(\pi,\cdot,V)$ and $f'=\sum_i\pi_i g(i,\cdot)$.
--
--   **Formalization Note** The printed "for every $a^*\in A$" is a typo for $a^*\in A^*$.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, Lemma 2.2

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, Lemma 2.2.

Let `f, f'` be real-valued functions on a finite nonempty chain `A`, and let `A*`, `A'*` be the sets
of maximizers of `f` and `f'` on `A`. If `f(a) − f(a') ≥ f'(a) − f'(a')` for every `a ≥ a'` in `A`,
then for every `a* ∈ A*` there exists `a'* ∈ A'*` with `a'* ≤ a*`, and for every `a'* ∈ A'*`
there exists `a* ∈ A*` with `a* ≥ a'*`.

**Formalization Note.** The paper's "for every `a* ∈ A`" is a typo for `a* ∈ A*`. -/
theorem lemma_2_2 {A : Type*} [Fintype A] [LinearOrder A] [Nonempty A] (f f' : A → ℝ)
    (h : ∀ a a' : A, a' ≤ a → f' a - f' a' ≤ f a - f a') :
    (∀ a ∈ argmaxSet f, ∃ b ∈ argmaxSet f', b ≤ a) ∧
      (∀ b ∈ argmaxSet f', ∃ a ∈ argmaxSet f, b ≤ a) := by sorry

end LovejoyPOMDP.Monotone
