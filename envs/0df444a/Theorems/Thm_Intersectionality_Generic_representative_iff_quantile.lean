-- Prove2me | Theorems.Thm_Intersectionality_Generic_representative_iff_quantile
-- name    : Intersectionality.Generic.representative_iff_quantile
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:16.71373+00:00
-- url     : https://prove2.me/theorems/dd961950-2bb8-4f0e-93d0-73a7eca0d019
-- title:
--   Proof of Theorem 1, (1)–(2) — with all p(g) > 0, (q, x*) is representative iff q_g(β_g) = x* for every g
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval, $n \in \mathbb{N}$, $\alpha \in (0,1)$, and let $Q$ be a rich and commutative family of increasing bijections of $X$. Let $p \in P$ give positive mass $p(g) > 0$ to every identity $g \in \{0,1\}^n$. For each $g$, let $\beta_g = F_g^{-1}(1-\alpha)$ be the $(1-\alpha)$-th quantile of the conditional score law. Let $q = (q_g)_g$ be a policy with every $q_g \in Q$, and let $x^* \in X$ be a threshold. Then
--
--   $$(q, x^*) \text{ yields a representative outcome at capacity } \alpha \iff q_g(\beta_g) = x^* \ \text{ for all } g \in G.$$
--
--   Here "representative" includes the capacity constraint $\sum_g \Pr(q_g(x) \ge x^* \mid g)\,p(g) = \alpha$. This is the reformulation of representativeness, condition (1), as condition (2) on quantiles. Part (a) of Theorem 1 uses the forward direction and part (b) the backward one.
--
--   **Formalization Note.** The page writes "(1) becomes (2)". The statement is the equivalence of representativeness (Definition 2 together with the capacity constraint) with (2), under the page's hypothesis that every $p(g) > 0$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 10 (PDF 11), proof of Theorem 1, displays (1)–(2)

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem representative_iff_quantile (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q)
    (p : DistSpace X n) (hpos : ∀ g, 0 < groupMass p.1 g)
    (q : Grp n → (↥X → ↥X)) (hqQ : ∀ g, q g ∈ Q) (xs : ↥X) :
    IsRepresentative p.1 α q xs ↔ ∀ g, q g (quantile p.1 α g) = xs := by sorry

end Intersectionality.Generic
