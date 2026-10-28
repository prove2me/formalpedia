-- Prove2me | Theorems.Thm_Intersectionality_Reductive_proposition_3
-- name    : Intersectionality.Reductive.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:43.851516+00:00
-- url     : https://prove2.me/theorems/246f3df8-d333-4a12-9ef6-cd027bb717ee
-- title:
--   Proposition 3 — on a nonempty open set of distributions some nonintersectional policy achieves a reductive representative outcome
-- statement:
--   A decision maker accepts a share $\alpha \in (0,1)$ of applicants. Each applicant has a score in an interval $X \subset \mathbb{R}$ and an identity $g \in \{0,1\}^n$, $n \ge 2$, and category $i$ consists of those with $g_i = 1$. $P$ is the space of joint laws of (score, identity) whose conditional score laws are continuous with full support on $X$, with the weak topology. Policies adjust group $g$'s scores by a map $q_g$ from a rich and commutative family $Q$ of strictly increasing bijections of $X$. A threshold $x^*$ then accepts the applicants with $q_g(x) \ge x^*$, subject to the capacity constraint that the accepted mass equals $\alpha$.
--
--   **Proposition 3.** There is a nonempty open set $U \subseteq P$ such that for every $p \in U$ there exist a nonintersectional policy $q = (q_g)_{g}$ with all $q_g \in Q$ and a threshold $x^* \in X$ that meet the capacity constraint and achieve a reductive representative outcome:
--   $$\hat p(g_i) = p(g_i) \qquad \text{for each identity dimension } i = 1, \dots, n.$$
--
--   Here $\hat p(g_i)$ is the share of category $i$ among the accepted and $p(g_i)$ its population share. The result contrasts with Theorem 1 of the same paper: nonintersectional policies generically cannot achieve representation of every intersectional group, but on an open set of distributions they can achieve representation along each identity dimension separately.
--
--   **Formalization Note.** $X$ is assumed to have at least two points; on a one-point $X$, $P$ is empty and no nonempty open set exists, and the paper's continuous conditional laws presuppose a nondegenerate interval. Openness and nonemptiness are in $P$ with its relative weak topology. "Reductive representative" includes the capacity constraint. Policies must lie in $Q$ group by group.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 16 (PDF 17), Proposition 3

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

namespace Intersectionality.Reductive

/-- Proposition 3, p. 16: for a nonempty open subset of distributions in `P`, there exists a
nonintersectional policy that achieves a reductive representative outcome. -/
theorem proposition_3 (X : Set ℝ) (hX : X.OrdConnected) (hXnt : X.Nontrivial) [Nonempty ↥X]
    (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∃ U : Set (Intersectionality.Generic.DistSpace X n), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      ∃ q : Intersectionality.Generic.Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ Intersectionality.Generic.IsNonintersectional q ∧
        ∃ xs : ↥X, IsReductiveRepresentative p.1 α q xs := by sorry

end Intersectionality.Reductive
