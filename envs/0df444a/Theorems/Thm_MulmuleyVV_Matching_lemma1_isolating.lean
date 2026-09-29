-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_lemma1_isolating
-- name    : MulmuleyVV.Matching.lemma1_isolating
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:34:51.532754+00:00
-- url     : https://prove2.me/theorems/97a5be5f-b298-4122-b786-b589a8dbaac2
-- title:
--   Lemma 1 (isolating lemma) — with weights uniform and independent in $[1, 2n]$, the minimum weight set is unique with probability $\ge 1/2$
-- statement:
--   Let $(S, F)$ be a set system with $|S| = n$ and $F$ a nonempty family of subsets of $S$. Assign to each element of $S$ an integer weight chosen uniformly and independently from $\{1, 2, \dots, 2n\}$. Then
--
--   $$
--   \Pr\bigl[\text{there is a unique minimum weight set in } F\bigr] \ \ge\ \frac12 .
--   $$
--
--   Equivalently, among the $(2n)^n$ weight functions $w : S \to \{1, \dots, 2n\}$, at least half give $F$ a unique minimum weight set.
--
--   This is the isolating lemma: random small weights single out one member of an arbitrary, possibly exponentially large, family. It is used in §4 with $S$ the edge set of a graph and $F$ its perfect matchings.
--
--   **Formalization Note** The probability is the fraction of the functions in `Fintype.piFinset (fun _ => Finset.Icc 1 (2n))`, stated without division as $(2n)^n \le 2\cdot\#\{w : \dots\}$. The hypothesis that $F$ is nonempty is added: the printed lemma omits it, and for $F = \emptyset$ there is no minimum weight set at all.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 107, Lemma 1

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem

namespace MulmuleyVV.Matching

open Classical in
theorem lemma1_isolating {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (hF : F.Nonempty) :
    (2 * Fintype.card α) ^ Fintype.card α ≤
      2 * ((Fintype.piFinset fun _ : α => Finset.Icc 1 (2 * Fintype.card α)).filter
        (fun w => HasUniqueMin F w)).card := by sorry

end MulmuleyVV.Matching
