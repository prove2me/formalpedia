-- Prove2me | Theorems.Thm_MallowsChoice_DP_theorem_1
-- name    : MallowsChoice.DP.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:45.323824+00:00
-- url     : https://prove2.me/theorems/6e1b64f0-86bf-4241-bfa9-80c4251a1271
-- title:
--   Theorem 1, p. 18 — Algorithm 2 computes exact Mallows choice probabilities
-- statement:
--   Let $n\ge1$ and $\theta\ge0$. Relabel the products so that the Mallows modal ranking is $a_1\cdots a_n$, and let the offer set $S$ contain $a_1$, as required by Algorithm 2's line 1. For every offered product $a_i\in S$, the output of Algorithm 2 equals its Mallows choice probability:
--
--   $$
--   P(a_i\mid S)=\sum_{s=1}^{n}\pi_{\mathrm{DP}}(i,s,n)
--   \qquad(a_i\in S).
--   $$
--
--   The same dynamic program assigns total zero to every $a_i\notin S$.
--
--   The theorem certifies that the polynomial-size recursion (3)–(4) produces the probabilities otherwise defined by a sum over all $n!$ rankings.
--
--   **Formalization Note** The algorithm's stated assumption $a_1\in S$ is a genuine restriction, despite the paper's “without loss of generality” wording. The zero-output clause records the table's behavior for unoffered products; equation (1), read literally for such a product, can be positive, so the equality with $P(a_i\mid S)$ is asserted only for offered products. The dynamic-program table is defined from the printed recursion, independently of the probabilistic $\pi$ used in the milestones.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), Algorithm 2 and Theorem 1, p. 18

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

namespace MallowsChoice.DP

open Finset

/-- Theorem 1, p. 18: Algorithm 2 computes the offered products' Mallows choice
probabilities; its table has zero total for every unoffered product. -/
theorem theorem_1 (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ)
    (S : Finset (Fin n)) (h1 : (⟨0, hn⟩ : Fin n) ∈ S) :
    (∀ a ∈ S, choiceProb θ S a =
      ∑ s ∈ Icc 1 n, piDP θ S (a.val + 1) s n) ∧
    (∀ a ∉ S, (∑ s ∈ Icc 1 n, piDP θ S (a.val + 1) s n) = 0) := by sorry

end MallowsChoice.DP
