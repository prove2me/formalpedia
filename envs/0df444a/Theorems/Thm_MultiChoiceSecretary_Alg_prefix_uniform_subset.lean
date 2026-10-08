-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_prefix_uniform_subset
-- name    : MultiChoiceSecretary.Alg.prefix_uniform_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:18.416321+00:00
-- url     : https://prove2.me/theorems/6ed54b05-db7e-4713-a952-5409fd3d40eb
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — the first m arrivals, m ~ B(n, 1/2), form a uniform random subset of S
-- statement:
--   Let $S$ be a finite set of $n$ real numbers revealed in a uniformly random order, and let $m \sim B(n, 1/2)$ be independent of the order. Let $Y$ be the set of the first $m$ arrivals. Then $Y$ is uniformly distributed on the $2^n$ subsets of $S$: for every $A \subseteq S$,
--
--   $$\Pr(Y = A) = 2^{-n}.$$
--
--   This is the first step of the proof sketch of Theorem 2.1; every later claim about $Y$ rests on it.
--
--   **Formalization Note.** $\Pr(Y = A)$ is the split average of the indicator of $\{Y = A\}$.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, proof sketch of Theorem 2.1, "Since m has distribution B(n, 1/2), it follows that Y is a sample from the uniform distribution on all 2^n subsets of S."

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem prefix_uniform_subset (S : Finset ℝ) :
    ∀ A ⊆ S, splitAvg S (fun Y => if Y = A then 1 else 0) = (1 / 2 : ℝ) ^ S.card := by sorry

end MultiChoiceSecretary.Alg
