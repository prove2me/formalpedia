-- Prove2me | Theorems.Thm_IwataFF_SFM_lemma_2_1
-- name    : IwataFF.SFM.lemma_2_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:28.416956+00:00
-- url     : https://prove2.me/theorems/b5bf60e4-f050-4b7d-a1e2-44c3c973e25c
-- title:
--   Lemma 2.1 — interchanging consecutive $v, u$ moves the extreme base by $\beta(\chi_u - \chi_v)$, and $\mathrm{ec}(y,u,v) = \beta$
-- statement:
--   Let $V$ be a finite nonempty set and $f$ a submodular function on the subsets of $V$ with $f(\emptyset) = 0$. Let $L$ be a linear ordering of $V$ that generates the extreme base $y \in B(f)$, and let $u, v \in V$ be such that $u$ immediately succeeds $v$ in $L$. Let $L'$ be obtained from $L$ by interchanging $u$ and $v$, and $y'$ the extreme base it generates. Then
--   $$y' = y + \beta(\chi_u - \chi_v), \qquad \beta = f(L(u) \setminus \{v\}) - f(L(u)) + y(v),$$
--   and moreover $\mathrm{ec}(y, u, v) = \beta$.
--
--   This lets the scaling algorithm compute an exchange capacity with one function evaluation and update an extreme base together with its ordering.
--
--   **Formalization Note** The lemma is stated for the order in which $v$ immediately precedes $u$ (the pair $(u,v)$ is *eligible*), as the sentence before the lemma and the term $L(u) \setminus \{v\}$ require; read with $u$ before $v$ the formula is false. $\mathrm{ec}$ is the supremum form of (2.1).
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 5, Lemma 2.1, (2.4), (2.5)

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic

namespace IwataFF.SFM

/-- Lemma 2.1 (arXiv:math/0004089v1, p. 5), for the eligible order: `v` immediately precedes
`u` in `L`. -/
theorem lemma_2_1 {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) (u v : α) (huv : ImmSucc L u v) :
    greedy f (swapAdj L u v) =
        greedy f L +
          (f ((prefixSet L u).erase v) - f (prefixSet L u) + greedy f L v) • (chi u - chi v) ∧
      ec V f (greedy f L) u v =
        f ((prefixSet L u).erase v) - f (prefixSet L u) + greedy f L v := by sorry

end IwataFF.SFM
