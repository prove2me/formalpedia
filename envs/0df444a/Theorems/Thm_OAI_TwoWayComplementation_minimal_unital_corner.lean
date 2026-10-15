-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_minimal_unital_corner
-- name    : OAI.TwoWayComplementation.minimal_unital_corner
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:53:40.008032+00:00
-- url     : https://prove2.me/theorems/64f131b5-55fe-41d2-b100-0cc75fa1fe3e
-- title:
--   A surjection from a finite semigroup onto a monoid restricts to a unital surjection on a corner that lifts all units
-- statement:
--   For an idempotent $d$ of a semigroup $A$, the corner $dAd=\{w\in A:\ dw=w=wd\}$ is a monoid under the multiplication of $A$, with identity element $d$.
--
--   **Theorem.** Let $A$ be a finite semigroup, $M$ a monoid and $\theta:A\to M$ a surjective multiplicative map, $\theta(ab)=\theta(a)\theta(b)$ for all $a,b\in A$. Then there are an idempotent $d\in A$ and a monoid homomorphism $\psi:dAd\to M$ such that $\psi$ is surjective,
--   $$
--   \psi(w)=\theta(w)\qquad\text{for all } w\in dAd,
--   $$
--   and every unit of $M$ is the image of a unit: for every unit $u$ of $M$ there is a unit $p$ of $dAd$ with $\psi(p)=u$.
--
--   In particular $\theta(d)=\psi(d)=1$. The theorem converts a surjective multiplicative map into a surjective monoid homomorphism with unit lifts, at the price of passing to a corner. In the complementation lower bound it turns a monoid of diagrams that maps onto all relations into a finite monoid with a unital homomorphism onto the relation monoid, in which every permutation graph lifts to a unit.
--
--   **Formalization Note** The corner is Mathlib's `IsIdempotentElem.Corner` with the monoid structure `cornerMonoid`, whose identity is $d$; $\theta$ is a `MulHom` and $\psi$ is a `MonoidHom`. The identity $\psi(w)=\theta(w)$ is stated for the underlying element `w.val` of $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean#L179-L206

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

open OAI OAI.TwoWayComplementation
universe u v
open scoped SetRel

theorem OAI.TwoWayComplementation.minimal_unital_corner {A M : Type*} [Semigroup A] [Finite A] [Monoid M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) :
    ∃ d : A, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* M,
      Function.Surjective ψ ∧ (∀ w, ψ w = θ w.val) ∧
      ∀ u : Mˣ, ∃ p : hd.Cornerˣ, ψ p = u.val := by sorry
