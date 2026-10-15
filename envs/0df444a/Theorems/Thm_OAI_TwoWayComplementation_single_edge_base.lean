-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_single_edge_base
-- name    : OAI.TwoWayComplementation.single_edge_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:51:46.159042+00:00
-- url     : https://prove2.me/theorems/09862b98-852f-4eba-a6bd-9cb618787fbb
-- title:
--   Base case: with at most 128 labels, an element representing one extra pair destroys a recurrent class
-- statement:
--   For a set $H$ let $\mathcal B(H)$ be the monoid of binary relations on $H$, with product $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\in H\}$ (composition in path order) and identity the equality relation $\mathrm{id}_H=\{(x,x):x\in H\}$.
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
--   Let $A$ be a monoid and let $\iota:A\to\mathcal D_m$ be a multiplicative map, $\iota(ab)=\iota(a)\iota(b)$ for all $a,b\in A$. It need not be unital: $\iota(1)$ is an idempotent diagram, not necessarily the identity, and every $\iota(a)$ lies in its corner. Let $\varphi:A\to\mathcal B(H)$ be a monoid homomorphism that is order reversing:
--   $$
--   \iota(a)\sqsubseteq\iota(b)\ \Longrightarrow\ \varphi(b)\subseteq\varphi(a)\qquad\text{for all }a,b\in A .
--   $$
--   Let $\beta(h)=2^{\lfloor (h-2)/127\rfloor}$, with truncated subtraction.
--
--   **Theorem.** If $|H|\le128$, and $a\in A$ satisfies $\varphi(a)=\mathrm{id}_H\cup\{(x,y)\}$ for some $x\ne y$ in $H$, then
--   $$
--   \beta(|H|)\le\big|\mathrm{Miss}_{\iota(1)}(\iota(a))\big| .
--   $$
--   Since $\beta(h)=1$ for $h\le128$, this says that $\iota(a)$ destroys at least one recurrent class of $\iota(1)$.
--
--   This is the base case of the induction on the number of labels that proves the exponential bound $\beta(|H|)\le|\mathrm{Miss}_{\iota(1)}(\iota(a))|$ for one-pair idempotents. The base case needs neither surjectivity of $\varphi$, nor unit lifts, nor idempotence of $a$.
--
--   **Formalization Note** $\beta$ is `lossBound`, $|H|$ is `Nat.card H`, $\sqsubseteq$ is membership in `Diagram.inclusion m`, and $\mathcal B(H)$ is `RelationMonoid H`. $\mathcal D_m$ is `Diagram m` with fields `forward`, `backward`, `left`, `right` and product `Diagram.comp`; the sign $+$ is `true` and $-$ is `false`. $\mathcal C(e)$ is `e.classes`, a set of pairs in `Bool × Set (Fin m)`, and $\mathrm{Miss}_e(z)$ is `e.missing z`. Cardinalities are `Set.ncard`, which is the true cardinality because these sets are finite. $H$ is not assumed finite: for infinite $H$ one has `Nat.card H = 0`, the hypothesis $|H|\le128$ holds trivially, and the conclusion still reads $1\le|\mathrm{Miss}_{\iota(1)}(\iota(a))|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean#L129-L147

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

theorem OAI.TwoWayComplementation.single_edge_base {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hreverse : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel)
    (a : A) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (hh : Nat.card H ≤ 128) :
    lossBound (Nat.card H) ≤ ((ι 1).missing (ι a)).ncard := by sorry
