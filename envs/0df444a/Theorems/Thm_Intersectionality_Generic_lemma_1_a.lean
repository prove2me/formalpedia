-- Prove2me | Theorems.Thm_Intersectionality_Generic_lemma_1_a
-- name    : Intersectionality.Generic.lemma_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:17.260985+00:00
-- url     : https://prove2.me/theorems/7b5a1474-2564-4e9c-9b08-ca4030b6a1e5
-- title:
--   Lemma 1(a) — each policy map in a rich commutative family of increasing bijections is continuous
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval and let $Q$ be a rich and commutative family of increasing bijections of $X$. Then
--
--   $$\text{every } q \in Q \text{ is continuous on } X.$$
--
--   This is the first of the structural properties of $Q$ that the proof of Theorem 1 relies on.
--
--   **Formalization Note.** $X$ is order-connected (an interval) and nonempty. Continuity is with respect to the subspace topology on $X$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 22 (PDF 23), Lemma 1(a)

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem lemma_1_a (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) : ∀ q ∈ Q, Continuous q := by sorry

end Intersectionality.Generic
