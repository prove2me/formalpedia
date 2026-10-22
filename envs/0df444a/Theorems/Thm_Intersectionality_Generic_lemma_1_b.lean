-- Prove2me | Theorems.Thm_Intersectionality_Generic_lemma_1_b
-- name    : Intersectionality.Generic.lemma_1_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:15.134502+00:00
-- url     : https://prove2.me/theorems/ca0a8986-6b11-4aef-8a6c-12c52ebae551
-- title:
--   Lemma 1(b) — the function in Q mapping x to y is unique
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval and let $Q$ be a rich and commutative family of increasing bijections of $X$. For all $x, y \in X$ and $q, q' \in Q$,
--
--   $$q(x) = y = q'(x) \implies q = q'.$$
--
--   Together with richness, this says that for each pair $x, y$ exactly one element of $Q$ sends $x$ to $y$. Commutativity is what makes this uniqueness hold.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 22 (PDF 23), Lemma 1(b)

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem lemma_1_b (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) :
    ∀ x y : ↥X, ∀ q ∈ Q, ∀ q' ∈ Q, q x = y → q' x = y → q = q' := by sorry

end Intersectionality.Generic
