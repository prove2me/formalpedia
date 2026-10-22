-- Prove2me | Theorems.Thm_Intersectionality_Generic_lemma_1_e
-- name    : Intersectionality.Generic.lemma_1_e
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:08.690981+00:00
-- url     : https://prove2.me/theorems/762b6112-a3cf-4251-875b-aa8f7e207bb9
-- title:
--   Lemma 1(e) — Q contains the inverse of each of its members
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval and let $Q$ be a rich and commutative family of increasing bijections of $X$. For every $q \in Q$ there is $q' \in Q$ with
--
--   $$q \circ q' = \mathrm{id}_X \quad\text{and}\quad q' \circ q = \mathrm{id}_X,$$
--
--   that is, $q^{-1} \in Q$. With (c) and (d), this makes $(Q,\circ)$ an abelian group.
--
--   **Formalization Note.** The inverse is stated as a two-sided inverse lying in $Q$ rather than through a choice-based inverse function.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 22 (PDF 23), Lemma 1(e)

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem lemma_1_e (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) :
    ∀ q ∈ Q, ∃ q' ∈ Q, q ∘ q' = id ∧ q' ∘ q = id := by sorry

end Intersectionality.Generic
