-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_pair_conjugate
-- name    : OAI.TwoWayComplementation.pair_conjugate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:49:31.665995+00:00
-- url     : https://prove2.me/theorems/b94c2e68-2ca5-4548-893d-455d5e87e2f6
-- title:
--   Conjugating a one-pair idempotent to any other off-diagonal pair at most doubles its cost
-- statement:
--   For a set $H$ let $\mathcal B(H)$ be the monoid of binary relations on $H$, with product $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\in H\}$ (composition in path order) and identity the equality relation $\mathrm{id}_H=\{(x,x):x\in H\}$. For a permutation $\sigma$ of $H$, its graph $G_\sigma=\{(x,\sigma(x)):x\in H\}$ is a unit of $\mathcal B(H)$ with inverse $G_{\sigma^{-1}}$.
--
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$. A *boundary diagram* is a quadruple $a=(a^{+},a^{-},a^{\mathrm L},a^{\mathrm R})$ of binary relations on $[m]$. They record traversals that enter on the left and exit on the right ($a^{+}$), enter on the right and exit on the left ($a^{-}$), or enter and exit on the left ($a^{\mathrm L}$) or on the right ($a^{\mathrm R}$). Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, and $R^{*}$ is the reflexive–transitive closure of $R$. The product
--   $$
--   ab=\Big(a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+},\ \ b^{-}(a^{\mathrm R}b^{\mathrm L})^{*}a^{-},\ \ a^{\mathrm L}\cup a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{\mathrm L}a^{-},\ \ b^{\mathrm R}\cup b^{-}a^{\mathrm R}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+}\Big)
--   $$
--   makes the set $\mathcal D_m$ of boundary diagrams a finite monoid with identity $(\mathrm{id},\mathrm{id},\varnothing,\varnothing)$. The corner of an idempotent $e$ is $\{z\in\mathcal D_m:\ ez=z=ze\}$.
--
--   For $e\in\mathcal D_m$ and a sign $s\in\{+,-\}$ put $K^{+}_e=(e^{\mathrm L}e^{\mathrm R})^{*}$, $K^{-}_e=(e^{\mathrm R}e^{\mathrm L})^{*}$ and $\mathrm{Rec}^{s}_e=K^{s}_e\,e^{s}\,K^{s}_e$. A *signed recurrent class* of $e$ is a pair $(s,C)$ such that, for some $x\in[m]$ with $(x,x)\in\mathrm{Rec}^{s}_e$, $C=\{y:\ (x,y)\in\mathrm{Rec}^{s}_e\text{ and }(y,x)\in\mathrm{Rec}^{s}_e\}$; let $\mathcal C(e)$ be the set of these classes. For $z\in\mathcal D_m$, the classes *missing* from $z$ relative to $e$ are
--   $$
--   \mathrm{Miss}_e(z)=\big\{(s,C)\in\mathcal C(e):\ (x,x)\notin K^{s}_e\,z^{s}\,K^{s}_e\ \text{ for every } x\in C\big\},
--   $$
--   the recurrent classes of $e$ none of whose loops survive when the through relation $e^{s}$ is replaced by $z^{s}$. For a finite set $X$, $|X|$ is its number of elements.
--
--   Let $A$ be a monoid and let $\iota:A\to\mathcal D_m$ be a multiplicative map, $\iota(ab)=\iota(a)\iota(b)$ for all $a,b\in A$. It need not be unital: $\iota(1)$ is an idempotent diagram, not necessarily the identity, and every $\iota(a)$ lies in its corner. Let $\varphi:A\to\mathcal B(H)$ be a monoid homomorphism such that permutations lift to units: for every permutation $\sigma$ of $H$ there is a unit $p$ of $A$ with $\varphi(p)=G_\sigma$.
--
--   **Theorem.** Let $a\in A$ be idempotent with $\varphi(a)=\mathrm{id}_H\cup\{(x,y)\}$ for some $x\neq y$ in $H$. Then for all $u\neq v$ in $H$ there is an idempotent $s\in A$ with
--   $$
--   \varphi(s)=\mathrm{id}_H\cup\{(u,v)\},\qquad \big|\mathrm{Miss}_{\iota(1)}(\iota(s))\big|\le 2\,\big|\mathrm{Miss}_{\iota(1)}(\iota(a))\big| .
--   $$
--
--   So one idempotent that represents a single off-diagonal pair yields idempotents for every other off-diagonal pair, with at most twice the cost. In the exponential lower bound this supplies the generators that realize the pairs from the left points to the hub and from the hub to the right points.
--
--   **Formalization Note** $\mathcal B(H)$ is `RelationMonoid H` with `toRel` giving the underlying relation, $G_\sigma$ is `(permutationUnit σ).val`, and $\mathrm{id}_H$ is `SetRel.id`. $\mathcal D_m$ is `Diagram m` with fields `forward`, `backward`, `left`, `right` and product `Diagram.comp`; the sign $+$ is `true` and $-$ is `false`. $\mathcal C(e)$ is `e.classes`, a set of pairs in `Bool × Set (Fin m)`, and $\mathrm{Miss}_e(z)$ is `e.missing z`. Cardinalities are `Set.ncard`, which is the true cardinality because these sets are finite. Neither $A$ nor $H$ is assumed finite, and $\varphi$ is not assumed surjective.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean#L149-L176

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.pair_conjugate {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hlift : ∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val)
    (a : A) (ha : IsIdempotentElem a) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (u v : H) (huv : u ≠ v) :
    ∃ s : A, IsIdempotentElem s ∧ (φ s).toRel = SetRel.id ∪ {(u, v)} ∧
      ((ι 1).missing (ι s)).ncard ≤ 2 * ((ι 1).missing (ι a)).ncard := by sorry
