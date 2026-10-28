-- Prove2me | Theorems.Thm_Intersectionality_Reductive_lemma_4
-- name    : Intersectionality.Reductive.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:04.619284+00:00
-- url     : https://prove2.me/theorems/669c6645-ee46-437e-b4c3-86cb4bf12533
-- title:
--   Lemma 4 — some distribution p̄ ∈ P satisfies (5)
-- statement:
--   Work in the model of the Setting: $X \subset \mathbb{R}$ a nondegenerate interval, $n \ge 2$, $\alpha \in (0,1)$, and $Q$ a rich and commutative family of strictly increasing bijections of $X$. For every base point $x_0 \in X$ there are a distribution $\bar p \in P$ and vectors $a, b \in X^n$ with $a_j \le b_j$ for all $j$ such that condition (5) holds for $\bar p$:
--   $$R_i(a_i, \theta_{-i}, t(a_i, \theta_{-i})) < \alpha < R_i(b_i, \theta_{-i}, t(b_i, \theta_{-i})) \quad \text{for all } i \text{ and all } \theta_{-i} \in \textstyle\times_{j \ne i} [a_j, b_j].$$
--
--   With Lemma 3 this produces the nonempty open set of Proposition 3.
--
--   **Formalization Note.** Two additions are disclosed. First, $X$ has at least two points: on a one-point $X$ no distribution has continuous conditional laws, $P$ is empty and the lemma is false. The paper's "continuous with full support on $X$" presupposes a nondegenerate interval. Second, $a \le b$ is part of the conclusion. Otherwise (5) could hold vacuously through empty boxes $\times_{j \ne i}[a_j, b_j]$; the paper's proof takes $a = (a, \dots, a)$, $b = (b, \dots, b)$ with $a < x_0 < b$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 25 (PDF 26), Lemma 4

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

namespace Intersectionality.Reductive

/-- Lemma 4, p. 25: there is a distribution `p̄ ∈ P` satisfying (5) for some `a ≤ b`. -/
theorem lemma_4 (X : Set ℝ) (hX : X.OrdConnected) (hXnt : X.Nontrivial) [Nonempty ↥X] (n : ℕ)
    (hn : 2 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x0 : ↥X, ∃ pbar : Intersectionality.Generic.DistSpace X n, ∃ a b : Fin n → ↥X,
      (∀ j, a j ≤ b j) ∧ Cond5 pbar.1 Q x0 α a b := by sorry

end Intersectionality.Reductive
