-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_common_pair_budget
-- name    : OAI.TwoWayComplementation.common_pair_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:46:16.568127+00:00
-- url     : https://prove2.me/theorems/5264ee9a-f8b0-4a4e-bd8d-9f7f60a1b384
-- title:
--   One common budget of missing classes for all sandwiched pair products
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
--   **Theorem.** Let $t,c\in\mathbb N$, let $s_0,\dots,s_{t-1}$ and $s'_0,\dots,s'_{t-1}$ be elements of $A$ each of which has cost at most $2c$,
--   $$
--   |\mathrm{Miss}_{\iota(1)}(\iota(s_i))|\le 2c,\qquad |\mathrm{Miss}_{\iota(1)}(\iota(s'_j))|\le 2c\qquad(0\le i,j<t),
--   $$
--   and let $b_0\in A$ be idempotent. Then there is a set $J_0\subseteq\mathcal C(\iota(b_0))$ of recurrent classes of $\iota(b_0)$ with $|J_0|\le 8tc$ such that
--   $$
--   \mathrm{Miss}_{\iota(b_0)}\big(\iota(b_0\,s_i\,s'_j\,b_0)\big)\subseteq J_0\qquad\text{for all } 0\le i,j<t .
--   $$
--
--   Thus all $t^2$ sandwiched products $b_0s_is'_jb_0$ destroy only classes from one fixed set whose size is linear in $t$. In the exponential lower bound this common budget lets $64^2$ successive edge insertions be paid for by the costs of only $128$ generators.
--
--   **Formalization Note** The two families are given as one map $f$ on `Bool × Fin t`, with $s_i=f(\mathrm{false},i)$ and $s'_j=f(\mathrm{true},j)$; the elements $s_i,s'_j$ need not be idempotent. $\mathcal D_m$ is `Diagram m` with fields `forward`, `backward`, `left`, `right` and product `Diagram.comp`; the sign $+$ is `true` and $-$ is `false`. $\mathcal C(e)$ is `e.classes`, a set of pairs in `Bool × Set (Fin m)`, and $\mathrm{Miss}_e(z)$ is `e.missing z`. Cardinalities are `Set.ncard`, which is the true cardinality because these sets are finite. The map $\iota$ is a non-unital `MulHom`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean#L50-L91

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

theorem OAI.TwoWayComplementation.common_pair_budget {A : Type*} [Monoid A] {m t c : ℕ}
    (ι : A →ₙ* Diagram m) (f : Bool × Fin t → A) (b0 : A) (hb0 : IsIdempotentElem b0)
    (hcost : ∀ p, ((ι 1).missing (ι (f p))).ncard ≤ 2 * c) :
    ∃ J0 ⊆ (ι b0).classes, J0.ncard ≤ 8 * t * c ∧
      ∀ i j, (ι b0).missing (ι (b0 * f (false, i) * f (true, j) * b0)) ⊆ J0 := by sorry
