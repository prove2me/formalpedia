-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_conjugate_missing_bound
-- name    : OAI.TwoWayComplementation.conjugate_missing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:45:47.279436+00:00
-- url     : https://prove2.me/theorems/a7448286-fe91-47a2-a09e-15b88312df5c
-- title:
--   Conjugating by a unit at most doubles the number of missing recurrent classes
-- statement:
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
--   Let $A$ be a monoid and let $\iota:A\to\mathcal D_m$ be a multiplicative map, $\iota(ab)=\iota(a)\iota(b)$ for all $a,b\in A$. It need not be unital: $\iota(1)$ is an idempotent diagram, not necessarily the identity, and every $\iota(a)$ lies in its corner.
--
--   **Theorem.** For every unit $p$ of $A$ and every $a\in A$,
--   $$
--   \big|\mathrm{Miss}_{\iota(1)}\big(\iota(p\,a\,p^{-1})\big)\big|\ \le\ 2\,\big|\mathrm{Miss}_{\iota(1)}\big(\iota(a)\big)\big| .
--   $$
--
--   The number $|\mathrm{Miss}_{\iota(1)}(\iota(a))|$ counts the recurrent classes of $\iota(1)$ destroyed by $\iota(a)$ and serves as the cost of $a$. The theorem says that this cost changes at most by a factor $2$ under conjugation by a unit. In the exponential lower bound for complementing two-way automata, it allows an element realizing one off-diagonal relation pair to be moved, by conjugation with permutation units, to elements realizing other pairs at no more than twice the cost.
--
--   **Formalization Note** $\mathcal D_m$ is `Diagram m` with fields `forward`, `backward`, `left`, `right` and product `Diagram.comp`; the sign $+$ is `true` and $-$ is `false`. $\mathcal C(e)$ is `e.classes`, a set of pairs in `Bool × Set (Fin m)`, and $\mathrm{Miss}_e(z)$ is `e.missing z`. Cardinalities are `Set.ncard`, which is the true cardinality because these sets are finite. The map $\iota$ is a `MulHom` (a non-unital multiplicative map) from $A$ to `Diagram m`, and $p^{-1}$ is the inverse of the unit `p : Aˣ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean#L31-L48

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

theorem OAI.TwoWayComplementation.conjugate_missing_bound {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (p : Aˣ) (a : A) :
    ((ι 1).missing (ι (p * a * (↑p⁻¹ : A)))).ncard ≤
      2 * ((ι 1).missing (ι a)).ncard := by sorry
