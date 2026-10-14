-- Prove2me | Theorems.Thm_Intersectionality_Generic_part_b_construction
-- name    : Intersectionality.Generic.part_b_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:23.936909+00:00
-- url     : https://prove2.me/theorems/6c883e0e-910f-4f85-b457-227c126fd456
-- title:
--   Proof of Theorem 1(b) — for every p ∈ P and x*, some policy in Q satisfies (2) and yields a representative outcome
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval, $n \in \mathbb{N}$, $\alpha \in (0,1)$, and let $Q$ be a rich and commutative family of increasing bijections of $X$. For every $p \in P$ and every threshold $x^* \in X$ there is a policy $q = (q_g)_g$ with the following three properties:
--   1. every $q_g \in Q$;
--   2. $q_g(\beta_g) = x^*$ for every group with $p(g) > 0$, where $\beta_g = F_g^{-1}(1-\alpha)$;
--   3. $(q, x^*)$ yields a representative outcome at capacity $\alpha$:
--
--   $$\sum_{g \in G} \Pr(q_g(x) \ge x^* \mid g)\,p(g) = \alpha, \qquad \hat p(g) = p(g) \ \text{ for all } g.$$
--
--   This is the construction of the intersectional policy in part (b) of Theorem 1.
--
--   **Formalization Note.** Groups with $p(g) = 0$ are allowed (convention C1). For them condition (2) is not required, since $\beta_g$ is undefined.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 10 (PDF 11), proof of Theorem 1, part (b), "Turning to part (b)"

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem part_b_construction (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q) :
    ∀ p : DistSpace X n, ∀ xs : ↥X, ∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧
      (∀ g, 0 < groupMass p.1 g → q g (quantile p.1 α g) = xs) ∧
      IsRepresentative p.1 α q xs := by sorry

end Intersectionality.Generic
