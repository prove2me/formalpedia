-- Prove2me | Theorems.Thm_Intersectionality_Generic_lemma_1_d
-- name    : Intersectionality.Generic.lemma_1_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:07.443978+00:00
-- url     : https://prove2.me/theorems/8d7dd3fe-e3ca-463c-8ac9-c9f34c72fcf0
-- title:
--   Lemma 1(d) — Q is closed under composition
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval and let $Q$ be a rich and commutative family of increasing bijections of $X$. Then
--
--   $$q, q' \in Q \implies q \circ q' \in Q.$$
--
--   Closure under composition is what lets a nonintersectional policy compose the category-wise maps $q_{e_i}$ and stay inside $Q$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 22 (PDF 23), Lemma 1(d)

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem lemma_1_d (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) : ∀ q ∈ Q, ∀ q' ∈ Q, q ∘ q' ∈ Q := by sorry

end Intersectionality.Generic
