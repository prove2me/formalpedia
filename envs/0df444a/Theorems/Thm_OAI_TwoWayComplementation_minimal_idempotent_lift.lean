-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_minimal_idempotent_lift
-- name    : OAI.TwoWayComplementation.minimal_idempotent_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:42:17.96709+00:00
-- url     : https://prove2.me/theorems/dce5a8e9-3d2c-49f0-95b5-73497c85c2d2
-- title:
--   An idempotent in the image of a finite semigroup has a minimal idempotent lift
-- statement:
--   Let $A$ be a finite semigroup, $M$ a semigroup, and $\theta:A\to M$ a surjective semigroup homomorphism, $\theta(xy)=\theta(x)\theta(y)$. Let $q\in M$ be idempotent, $q^2=q$. An *idempotent lift* of $q$ is an element $d\in A$ with $d^2=d$ and $\theta(d)=q$.
--
--   **Theorem.** There is an idempotent lift $d$ of $q$ that is minimal among the idempotent lifts of $q$: for every $e\in A$,
--   $$
--   e^2=e,\quad \theta(e)=q,\quad ed=e,\quad de=e\qquad\Longrightarrow\qquad e=d .
--   $$
--
--   The relation $ed=e=de$ is the natural partial order $e\le d$ on idempotents (equivalently, $e$ lies in the corner $dAd$), so no idempotent lift of $q$ lies strictly below $d$. Minimal lifts are the base points at which the restriction of $\theta$ to corner monoids reflects units; for a surjection onto a monoid, the minimal lift of the identity yields a unital corner map in which every unit of the target has a unit preimage.
--
--   **Formalization Note** $\theta$ is a non-unital multiplicative map `A →ₙ* M` between semigroups (no identity elements are required), surjectivity is `Function.Surjective θ`, and idempotence is `IsIdempotentElem`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean#L99-L124

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.minimal_idempotent_lift {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) (q : M) (hq : IsIdempotentElem q) :
    ∃ d, IsIdempotentElem d ∧ θ d = q ∧
      ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d := by sorry
