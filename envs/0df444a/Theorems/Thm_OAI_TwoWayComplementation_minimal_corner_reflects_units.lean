-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_minimal_corner_reflects_units
-- name    : OAI.TwoWayComplementation.minimal_corner_reflects_units
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:43:01.448124+00:00
-- url     : https://prove2.me/theorems/888066d5-c72a-45c4-b9e3-4704b1910de9
-- title:
--   At a minimal idempotent lift, the restricted corner homomorphism reflects units
-- statement:
--   Let $A$ be a finite semigroup, $M$ a semigroup and $\theta:A\to M$ a semigroup homomorphism. For an idempotent $x$ of a semigroup $S$, the corner $xSx=\{y\in S:xy=y=yx\}$ is a monoid under the multiplication of $S$, with identity element $x$.
--
--   Let $d\in A$ and $q\in M$ be idempotents with $\theta(d)=q$, and assume that $d$ is minimal among the idempotent lifts of $q$:
--   $$
--   \text{for all } e\in A:\qquad e^2=e,\ \ \theta(e)=q,\ \ ed=e,\ \ de=e\ \Longrightarrow\ e=d .
--   $$
--   Then $\theta$ restricts to a monoid homomorphism $\theta_d:dAd\to qMq$, $\theta_d(w)=\theta(w)$.
--
--   **Theorem.** If $w\in dAd$ and $\theta_d(w)$ is a unit of the monoid $qMq$, then $w$ is a unit of the monoid $dAd$.
--
--   So at a minimal idempotent lift the restricted corner homomorphism reflects units. Surjectivity of $\theta$ is not needed here. Combined with the fact that $\theta_d$ is surjective when $\theta$ is, it produces unital corner maps in which every unit of the target has a unit preimage, a property used in the inductive bounds on lost classes.
--
--   **Formalization Note** The corner is Mathlib's `IsIdempotentElem.Corner` (the subsemigroup `Subsemigroup.corner d`), made into a monoid with identity $d$; $\theta_d$ is `cornerMap θ hd hq hθd`, and both units are `IsUnit` in the corner monoids.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean#L161-L178

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.minimal_corner_reflects_units {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) {d : A} {q : M} (hd : IsIdempotentElem d) (hq : IsIdempotentElem q)
    (hθd : θ d = q)
    (hminimal : ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d)
    (w : hd.Corner) (hw : IsUnit (cornerMap θ hd hq hθd w)) : IsUnit w := by sorry
