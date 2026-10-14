-- Prove2me | Theorems.Thm_Intersectionality_Reductive_lemma_3
-- name    : Intersectionality.Reductive.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:11.015977+00:00
-- url     : https://prove2.me/theorems/379e093b-2f7c-4a24-89ff-50c5e52fbad9
-- title:
--   Lemma 3 — condition (5) at p̄ holds on a neighbourhood of p̄ in P
-- statement:
--   Work in the model of the Setting: $X \subset \mathbb{R}$ an interval, $n \ge 2$, $\alpha \in (0,1)$, and $Q$ a rich and commutative family of strictly increasing bijections of $X$. Fix $x_0 \in X$. Suppose $\bar p \in P$ and $a, b \in X^n$ satisfy condition (5):
--   $$R_i(a_i, \theta_{-i}, t(a_i, \theta_{-i})) < \alpha < R_i(b_i, \theta_{-i}, t(b_i, \theta_{-i})) \quad \text{for all } i \text{ and all } \theta_{-i} \in \textstyle\times_{j \ne i} [a_j, b_j].$$
--   Then every $p$ in some neighbourhood of $\bar p$ in $P$ (weak topology) also satisfies (5) with the same $a, b$.
--
--   This stability lemma is what turns a single distribution satisfying (5) into a nonempty open set of them in Proposition 3.
--
--   **Formalization Note.** "Neighbourhood" is in the relative weak topology of $P$. The functions $R_i$ and $t$ are those of the distribution $p$ under consideration.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 25 (PDF 26), Lemma 3

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

open Filter Topology

namespace Intersectionality.Reductive

/-- Lemma 3, p. 25: if `p̄ ∈ P` satisfies (5) for some `a, b ∈ Xⁿ`, then (5) is satisfied by all
`p` in a neighbourhood of `p̄` (in `P`). -/
theorem lemma_3 (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ (x0 : ↥X) (pbar : Intersectionality.Generic.DistSpace X n) (a b : Fin n → ↥X),
      Cond5 pbar.1 Q x0 α a b → ∀ᶠ p in 𝓝 pbar, Cond5 p.1 Q x0 α a b := by sorry

end Intersectionality.Reductive
