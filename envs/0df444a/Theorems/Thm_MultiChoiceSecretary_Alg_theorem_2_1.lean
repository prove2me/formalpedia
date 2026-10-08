-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_theorem_2_1
-- name    : MultiChoiceSecretary.Alg.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:48.981702+00:00
-- url     : https://prove2.me/theorems/6feb7d53-d40a-42e4-84f3-6b6c0f1dc7d2
-- title:
--   Theorem 2.1, PDF p. 2 — the recursive k-choice secretary algorithm selects expected value ≥ (1 − 5/√k)·v
-- statement:
--   Let $S$ be any set of $n$ non-negative real numbers, revealed one at a time in a uniformly random order, let $k \ge 1$ be the number of allowed selections, and let $v$ be the sum of the $k$ largest elements of $S$ (all of $S$ if $k > n$). Kleinberg's recursive algorithm uses the classical secretary rule for $k = 1$; for $k \ge 2$ it draws $m \sim B(n,1/2)$, recursively selects up to $\lfloor k/2\rfloor$ elements among the first $m$ arrivals, and afterwards selects every arrival exceeding $y_{\lfloor k/2\rfloor}$, the $\lfloor k/2\rfloor$-th largest of the first $m$ values, until $k$ elements have been selected in total. Then the expected sum of the selected elements, over the random order and all internal coin tosses, satisfies
--
--   $$\mathbb E\Big[\sum_{x \text{ selected}} x\Big] \;\ge\; \Big(1 - \frac{5}{\sqrt k}\Big)v.$$
--
--   This shows that the competitive ratio of the $k$-choice secretary problem tends to $1$ as $k \to \infty$, at rate $1 - O(1/\sqrt k)$; it is the main result of the paper and the basis of its strategyproof online auction.
--
--   **Formalization Note.** When the first phase has seen fewer than $\lfloor k/2\rfloor$ arrivals, the page leaves $y_{\lfloor k/2\rfloor}$ undefined; the formalization reads it as $-\infty$, so every later arrival is selected until the cap. The cap of $k$ counts the selections of both phases. For $k \le 25$ the right-hand side is $\le 0$ and the claim is immediate; it is stated uniformly in $k$, as on the page.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, Theorem 2.1

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem theorem_2_1 (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (1 - 5 / Real.sqrt k) * topSum S k ≤ expectedValue S k := by sorry

end MultiChoiceSecretary.Alg
