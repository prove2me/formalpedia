-- Prove2me | Theorems.Thm_FuzzyGames_Walras_theorem_4_1
-- name    : FuzzyGames.Walras.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:11.083985+00:00
-- url     : https://prove2.me/theorems/9f2f807b-13ae-48dc-a79f-31050ac67003
-- title:
--   Theorem 4.1 — the fuzzy core of an exchange economy coincides with the set of Walras equilibria
-- statement:
--   Consider an exchange economy with $n$ consumers and $l$ commodities in which every consumer $i$ has consumption set $\mathbb{R}^l_+$, a preference relation $\succcurlyeq_i$ and an endowment set $Y(i) \subset \mathbb{R}^l$. Assume (assumption (1) of §4 and the standing assumptions of the section):
--
--   1. each $Y(i)$ is closed, convex and comprehensive;
--   2. each $\succcurlyeq_i$ is a continuous, convex, complete preorder on $\mathbb{R}^l_+$ with $x \succ_i y \Rightarrow \alpha x + (1-\alpha)y \succ_i y$ for $\alpha \in\, ]0,1[$;
--   3. no consumer is satiated;
--   4. every $Y(i)$ contains a strictly positive vector.
--
--   A fuzzy coalition $\tau \in [0,1]^n$ disposes of $Y(\tau) = \sum_i \tau_i Y(i)$, and $x \in X(N)$ is in the **fuzzy core** if no nonzero $\tau$ has an allocation $x_\tau$, $x_\tau^i \in \mathbb{R}^l_+$, $\sum_i \tau_i x_\tau^i \in Y(\tau)$, with $x_\tau^i \succ_i x^i$ for all $i$ with $\tau_i > 0$. An allocation $\bar x \in X(N)$ is a **Walras equilibrium** if some price $\bar p \in \mathbb{R}^l$ satisfies $\bar p\cdot \bar x^i = r_i(\bar p) = \sup_{y \in Y(i)} \bar p \cdot y$ and $\bar x^i \succcurlyeq_i x$ for all $x \in \mathbb{R}^l_+$ with $\bar p \cdot x \le r_i(\bar p)$, for every $i$. Then
--   $$\text{fuzzy core} = \{\text{Walras equilibria}\}.$$
--
--   This is Aubin's fuzzy-coalition version of the Debreu–Scarf core equivalence theorem: in place of a limit of replica economies, it is the admission of every fuzzy coalition that shrinks the core down to the competitive allocations, for an economy with a fixed finite number of consumers.
--
--   **Formalization Note.** Every convention of the definitions file applies: complete preorders (the paper's "preference preordering"), closed contour sets as continuity, (1)(i) read with $x \succ y$ in the premise, strict improvement and $\tau \neq 0$ in the fuzzy core, incomes in `EReal`.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Theorem 4.1, p. 6

import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic

namespace FuzzyGames.Walras

/-- Theorem 4.1 (Aubin 1981, p. 6): under assumption (1), the fuzzy core of the economy
coincides with the set of Walras equilibria. -/
theorem theorem_4_1 {n l : ℕ} (E : Economy n l) (hE : E.Assumptions) :
    E.fuzzyCore = E.walras := by sorry

end FuzzyGames.Walras
