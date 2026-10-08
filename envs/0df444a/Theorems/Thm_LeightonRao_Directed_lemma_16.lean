-- Prove2me | Theorems.Thm_LeightonRao_Directed_lemma_16
-- name    : LeightonRao.Directed.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:31.769645+00:00
-- url     : https://prove2.me/theorems/f3942574-9b2f-45b5-8e06-3a8444255850
-- title:
--   Lemma 16, p. 807 — a distance function satisfying the directed distance constraint yields a directed cut of ratio cost O(W log n)
-- statement:
--   Let $G$ be a strongly connected directed network on $n\ge2$ nodes and $d\ge0$ a distance function with total weight $W$ that satisfies the directed distance constraint $\sum_{(u,v)\in V^2}d(u,v)\ge1$. Then there is a nonempty proper $U\subsetneq V$ with
--   $$\frac{C(U,\bar U)}{|U|\,|\bar U|}\le\frac{1152}{5}\,W\log n,$$
--   $\log$ to base $2$.
--
--   Applied to an optimal dual solution ($W=f$), it gives $\mathcal S=O(f\log n)$, the lower bound of Theorem 12.
--
--   **Formalization Note** The paper states "ratio cost $O(W\log n)$". The constant $1152/5$ is Corollary 14's bound $8W\log n/(\Delta(n/6)(5n/6))$ at $\Delta=1/(4n^2)$; it dominates Lemma 15's $12W$ because $\log n\ge1$ for $n\ge2$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 807, Lemma 16

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Lemma 16, p. 807. A nonnegative distance function of total weight `W` satisfying
the directed distance constraint yields a directed cut of ratio cost at most `(1152/5) W log₂ n`
(Corollary 14's bound; it dominates Lemma 15's `12 W` since `log₂ n ≥ 1`). -/
theorem lemma_16 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (hW : SatisfiesDiConstraint N d) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      diRatio N U ≤ (1152 / 5) * diTotalWeight N d * Real.logb 2 (Fintype.card V) := by sorry

end LeightonRao.Directed
