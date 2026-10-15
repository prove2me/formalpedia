-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_order_reversing_image_bound_finite
-- name    : OAI.TwoWayComplementation.order_reversing_image_bound_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:54:29.703367+00:00
-- url     : https://prove2.me/theorems/90b187f8-4be7-448f-80e1-74bc91fcf494
-- title:
--   Order-reversing maps from boundary-diagram monoids onto all relations need exponentially many labels
-- statement:
--   For a set $H$ let $\mathcal B(H)$ be the monoid of binary relations on $H$, with product $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\in H\}$ (composition in path order) and identity the equality relation $\mathrm{id}_H=\{(x,x):x\in H\}$.
--
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$. A *boundary diagram* is a quadruple $a=(a^{+},a^{-},a^{\mathrm L},a^{\mathrm R})$ of binary relations on $[m]$. They record traversals that enter on the left and exit on the right ($a^{+}$), enter on the right and exit on the left ($a^{-}$), or enter and exit on the left ($a^{\mathrm L}$) or on the right ($a^{\mathrm R}$). Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, and $R^{*}$ is the reflexive–transitive closure of $R$. The product
--   $$
--   ab=\Big(a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+},\ \ b^{-}(a^{\mathrm R}b^{\mathrm L})^{*}a^{-},\ \ a^{\mathrm L}\cup a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{\mathrm L}a^{-},\ \ b^{\mathrm R}\cup b^{-}a^{\mathrm R}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+}\Big)
--   $$
--   makes the set $\mathcal D_m$ of boundary diagrams a finite monoid with identity $(\mathrm{id},\mathrm{id},\varnothing,\varnothing)$. The corner of an idempotent $e$ is $\{z\in\mathcal D_m:\ ez=z=ze\}$. For $a,b\in\mathcal D_m$ write $a\sqsubseteq b$ if $a^{+}\subseteq b^{+}$, $a^{-}\subseteq b^{-}$, $a^{\mathrm L}\subseteq b^{\mathrm L}$ and $a^{\mathrm R}\subseteq b^{\mathrm R}$ (componentwise inclusion).
--
--   **Theorem.** Let $H$ be a finite set with $|H|\ge2$, and let $m\ge1$. Let $S\subseteq\mathcal D_m$ contain the identity diagram and be closed under the product, and let $\varphi:S\to\mathcal B(H)$ be a map such that
--   1. $\varphi$ is surjective onto the set of all binary relations on $H$;
--   2. $\varphi$ is multiplicative: $\varphi(ab)=\varphi(a)\,\varphi(b)$ for all $a,b\in S$, where the right side is composition in path order;
--   3. $\varphi$ is order reversing: $a\sqsubseteq b$ implies $\varphi(b)\subseteq\varphi(a)$, for all $a,b\in S$.
--
--   Then
--   $$
--   2^{\lfloor (|H|-2)/127\rfloor}\le 2m .
--   $$
--
--   Equivalently, $m\ge\frac12\cdot2^{\lfloor(|H|-2)/127\rfloor}$. In the complementation lower bound, $H$ has $n-2$ points and $S$ consists of the boundary diagrams, with $m=s+1$ labels, of the input words of an $s$-state two-way automaton recognizing the complement of the source language; $\varphi$ sends the diagram of a word to the relational product of its letters. The theorem then gives $2^{\lfloor (n-4)/127\rfloor}\le2(s+1)$.
--
--   **Formalization Note** $\mathcal D_m$ is `Diagram m` with product `Diagram.comp` and identity `Diagram.identity m`, and $\sqsubseteq$ is `Diagram.inclusion m`. $\varphi$ is a function on the subtype $S$ with values in `SetRel H H`; it is not required to map the identity diagram to the identity relation. $|H|$ is `Nat.card H`, and the left side is `lossBound (Nat.card H)`, computed with natural-number subtraction and division. The hypothesis $m\ge1$ is part of the statement but is not used in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean#L218-L265

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

theorem OAI.TwoWayComplementation.order_reversing_image_bound_finite {H : Type*} [Finite H]
    (m : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ Nat.card H)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel H H) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound (Nat.card H) ≤ 2 * m := by sorry
