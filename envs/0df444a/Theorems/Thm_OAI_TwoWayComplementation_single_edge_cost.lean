-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_single_edge_cost
-- name    : OAI.TwoWayComplementation.single_edge_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:52:55.395563+00:00
-- url     : https://prove2.me/theorems/3afe02a0-8a53-4d11-ab8d-77b2b77abcbc
-- title:
--   Exponential cost of a single relation pair: at least $2^{\lfloor (h-2)/127\rfloor}$ missing recurrent classes
-- statement:
--   For a set $H$ let $\mathcal B(H)$ be the monoid of binary relations on $H$, with product $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\in H\}$ (composition in path order) and identity the equality relation $\mathrm{id}_H=\{(x,x):x\in H\}$. For a permutation $\sigma$ of $H$, its graph $G_\sigma=\{(x,\sigma(x)):x\in H\}$ is a unit of $\mathcal B(H)$ with inverse $G_{\sigma^{-1}}$.
--
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$. A *boundary diagram* is a quadruple $a=(a^{+},a^{-},a^{\mathrm L},a^{\mathrm R})$ of binary relations on $[m]$. They record traversals that enter on the left and exit on the right ($a^{+}$), enter on the right and exit on the left ($a^{-}$), or enter and exit on the left ($a^{\mathrm L}$) or on the right ($a^{\mathrm R}$). Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, and $R^{*}$ is the reflexive–transitive closure of $R$. The product
--   $$
--   ab=\Big(a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+},\ \ b^{-}(a^{\mathrm R}b^{\mathrm L})^{*}a^{-},\ \ a^{\mathrm L}\cup a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{\mathrm L}a^{-},\ \ b^{\mathrm R}\cup b^{-}a^{\mathrm R}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+}\Big)
--   $$
--   makes the set $\mathcal D_m$ of boundary diagrams a finite monoid with identity $(\mathrm{id},\mathrm{id},\varnothing,\varnothing)$. The corner of an idempotent $e$ is $\{z\in\mathcal D_m:\ ez=z=ze\}$. For $a,b\in\mathcal D_m$ write $a\sqsubseteq b$ if $a^{+}\subseteq b^{+}$, $a^{-}\subseteq b^{-}$, $a^{\mathrm L}\subseteq b^{\mathrm L}$ and $a^{\mathrm R}\subseteq b^{\mathrm R}$ (componentwise inclusion).
--
--   For $e\in\mathcal D_m$ and a sign $s\in\{+,-\}$ put $K^{+}_e=(e^{\mathrm L}e^{\mathrm R})^{*}$, $K^{-}_e=(e^{\mathrm R}e^{\mathrm L})^{*}$ and $\mathrm{Rec}^{s}_e=K^{s}_e\,e^{s}\,K^{s}_e$. A *signed recurrent class* of $e$ is a pair $(s,C)$ such that, for some $x\in[m]$ with $(x,x)\in\mathrm{Rec}^{s}_e$, $C=\{y:\ (x,y)\in\mathrm{Rec}^{s}_e\text{ and }(y,x)\in\mathrm{Rec}^{s}_e\}$; let $\mathcal C(e)$ be the set of these classes. For $z\in\mathcal D_m$, the classes *missing* from $z$ relative to $e$ are
--   $$
--   \mathrm{Miss}_e(z)=\big\{(s,C)\in\mathcal C(e):\ (x,x)\notin K^{s}_e\,z^{s}\,K^{s}_e\ \text{ for every } x\in C\big\},
--   $$
--   the recurrent classes of $e$ none of whose loops survive when the through relation $e^{s}$ is replaced by $z^{s}$. For a finite set $X$, $|X|$ is its number of elements.
--
--   **Theorem.** Let $h\ge2$. Let $A$ be a finite monoid and $H$ a finite set with $|H|=h$. Let $\iota:A\to\mathcal D_m$ be a multiplicative map, $\iota(ab)=\iota(a)\iota(b)$ (not necessarily unital), and let $\varphi:A\to\mathcal B(H)$ be a monoid homomorphism such that
--   1. $\varphi$ is surjective;
--   2. $\varphi$ is order reversing: $\iota(a)\sqsubseteq\iota(b)$ implies $\varphi(b)\subseteq\varphi(a)$, for all $a,b\in A$;
--   3. permutations lift to units: for every permutation $\sigma$ of $H$ there is a unit $p$ of $A$ with $\varphi(p)=G_\sigma$.
--
--   Then for every idempotent $a\in A$ and all $x\ne y$ in $H$ with $\varphi(a)=\mathrm{id}_H\cup\{(x,y)\}$,
--   $$
--   2^{\lfloor (h-2)/127\rfloor}\le\big|\mathrm{Miss}_{\iota(1)}(\iota(a))\big| .
--   $$
--
--   So an idempotent that represents a single off-diagonal pair must destroy exponentially many recurrent classes of $\iota(1)$. Since a diagram in $\mathcal D_m$ has at most $2m$ signed recurrent classes, this forces $m$ to be exponentially large in $h$. This is the source of the exponential lower bound for complementing two-way nondeterministic automata.
--
--   **Formalization Note** The statement fixes $h$ first and then quantifies over all types $A$ and $H$ in fixed universes, so that strong induction on $h$ can be applied to a corner monoid of $A$ and a subset of $H$. $|H|$ is `Nat.card H`, the left side is `lossBound h` (natural-number subtraction and division), $\sqsubseteq$ is `Diagram.inclusion m`, $\mathcal B(H)$ is `RelationMonoid H`, and $G_\sigma$ is `(permutationUnit σ).val`. $\mathcal D_m$ is `Diagram m` with fields `forward`, `backward`, `left`, `right` and product `Diagram.comp`; the sign $+$ is `true` and $-$ is `false`. $\mathcal C(e)$ is `e.classes`, a set of pairs in `Bool × Set (Fin m)`, and $\mathrm{Miss}_e(z)$ is `e.missing z`. Cardinalities are `Set.ncard`, which is the true cardinality because these sets are finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean#L11-L177

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

theorem OAI.TwoWayComplementation.single_edge_cost (h : ℕ) :
    ∀ {A : Type u} {H : Type v} [Monoid A] [Finite A] [Finite H] {m : ℕ},
      Nat.card H = h → 2 ≤ h →
      ∀ (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H), Function.Surjective φ →
      (∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel) →
      (∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val) →
      ∀ a, IsIdempotentElem a → ∀ x y : H, x ≠ y →
      (φ a).toRel = SetRel.id ∪ {(x, y)} →
      lossBound h ≤ ((ι 1).missing (ι a)).ncard := by sorry
