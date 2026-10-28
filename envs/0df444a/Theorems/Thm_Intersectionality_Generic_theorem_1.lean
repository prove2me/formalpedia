-- Prove2me | Theorems.Thm_Intersectionality_Generic_theorem_1
-- name    : Intersectionality.Generic.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:17.581482+00:00
-- url     : https://prove2.me/theorems/66e88b34-196e-4e8f-b106-b7daf43a2d00
-- title:
--   Theorem 1 — for generic distributions no nonintersectional policy yields a representative outcome, and an intersectional one does
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval of scores and $G = \{0,1\}^n$ with $n \ge 2$ the identities. Let $\alpha \in (0,1)$ be the share of applicants accepted, and let $Q$ be a rich and commutative family of increasing bijections of $X$. Let $P$ be the space of joint score–identity distributions whose conditional score laws are continuous with full support on $X$, with the relative weak$^*$ topology. A policy is a vector $(q_g)_{g\in G}$ with every $q_g \in Q$. It *yields a representative outcome* at $p$ if some threshold $x^* \in X$ makes three things hold:
--   - the accepted applicants are those with $q_g(x) \ge x^*$;
--   - the capacity constraint $\sum_g \Pr(q_g(x) \ge x^* \mid g)\,p(g) = \alpha$ holds;
--   - every group's share among the accepted equals its population share $p(g)$.
--
--   **Theorem 1.** There is a dense open subset $U \subseteq P$ such that for every $p \in U$:
--
--   $$\text{(a) no nonintersectional policy yields a representative outcome at } p;$$
--   $$\text{(b) some intersectional policy yields a representative outcome at } p.$$
--
--   Nonintersectional means $q_g = q_{g'} \circ q_{g''}$ whenever $g = g' + g''$, and intersectional means not nonintersectional. The theorem says that policies built from independent adjustments along each identity dimension generically fail to produce proportional representation of the intersectional groups, while policies designed group by group succeed.
--
--   **Formalization Note.** "Generic" is "holds on a dense open subset" (p. 9), with openness and density taken in $P$ itself. Both parts hold on one common set $U$. The hypotheses $n \ge 2$ and $\alpha \in (0,1)$ are those of p. 7. $X$ is assumed nonempty and order-connected. Groups with $p(g) = 0$ are unconstrained in $P$ (convention C1).
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 9 (PDF 10), Theorem 1

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem theorem_1 (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q) :
    ∃ U : Set (DistSpace X n), IsOpen U ∧ Dense U ∧ ∀ p ∈ U,
      (¬ ∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ IsNonintersectional q ∧
          ∃ xs : ↥X, IsRepresentative p.1 α q xs) ∧
      (∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ ¬ IsNonintersectional q ∧
          ∃ xs : ↥X, IsRepresentative p.1 α q xs) := by sorry

end Intersectionality.Generic
