-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_diagram_recognition_lower_bound
-- name    : OAI.TwoWayComplementation.diagram_recognition_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:00:39.106064+00:00
-- url     : https://prove2.me/theorems/1540e492-28a8-4cf9-a46e-ad64b91c8ea7
-- title:
--   Recognizing empty relation products on $h$ points through diagrams on $m$ labels forces $2^{\lfloor (h-2)/127\rfloor}\le 2m$
-- statement:
--   For $m\in\mathbb{N}$ let $[m]=\{0,1,\dots,m-1\}$. Binary relations are composed in path order, $(x,z)\in PQ$ iff $(x,y)\in P$ and $(y,z)\in Q$ for some $y$, and $P^{*}$ denotes the reflexive–transitive closure of a relation $P$ on a set. A boundary diagram on $m$ labels is a quadruple $a=(F_a,B_a,L_a,R_a)$ of relations on $[m]$, read as the connections of a two-sided gadget: forward (enter on the left, leave on the right), backward (enter on the right, leave on the left), left return (enter and leave on the left) and right return (enter and leave on the right). The diagrams form a monoid $\mathcal{D}_m$ under the path-order product
--   $$
--   \begin{aligned}
--   F_{ab}&=F_a(L_bR_a)^{*}F_b, & B_{ab}&=B_b(R_aL_b)^{*}B_a,\\
--   L_{ab}&=L_a\cup F_a(L_bR_a)^{*}L_bB_a, & R_{ab}&=R_b\cup B_bR_a(L_bR_a)^{*}F_b,
--   \end{aligned}
--   $$
--   with identity $\mathbf{1}=(\mathrm{id},\mathrm{id},\varnothing,\varnothing)$, and they are ordered componentwise: $a\sqsubseteq a'$ means $F_a\subseteq F_{a'}$, $B_a\subseteq B_{a'}$, $L_a\subseteq L_{a'}$ and $R_a\subseteq R_{a'}$.
--
--   For $h\in\mathbb{N}$, let $\mathrm{Rel}([h])$ be the set of binary relations on $[h]$, used as an alphabet. For a word $w=X_1\cdots X_k$ over $\mathrm{Rel}([h])$, let $\pi(w)=X_1\cdots X_k$ be the composite relation in path order, with $\pi(\varepsilon)=\mathrm{id}$ for the empty word $\varepsilon$.
--
--   Let $h\ge2$ and $m\ge1$ be natural numbers, and let $\tau$ assign a diagram $\tau(w)\in\mathcal{D}_m$ to every word $w$ over $\mathrm{Rel}([h])$ such that $\tau(\varepsilon)=\mathbf{1}$ and $\tau(uv)=\tau(u)\,\tau(v)$ for all words $u,v$. Suppose there are diagrams $l,r\in\mathcal{D}_m$ and labels $a,b\in[m]$ such that for every word $w$
--   $$
--   (a,b)\in F_{l\,\tau(w)\,r}\iff \pi(w)=\varnothing .
--   $$
--   Then
--   $$
--   2^{\lfloor (h-2)/127\rfloor}\le 2m .
--   $$
--
--   This is the lower bound in diagram form: recognizing, through products of diagrams on $m$ labels, the words of relations on $h$ points whose product is empty requires $m$ exponential in $h$. Every two-way nondeterministic automaton with $s$ states has a multiplicative diagram representation on $s+1$ labels; applied, for $n\ge4$, to an automaton for the complement of the language of words with nonempty product on $\{0,\dots,n-3\}$, which is recognized by an $n$-state automaton, the bound yields $2^{\lfloor (n-4)/127\rfloor}\le 2(s+1)$.
--
--   **Formalization Note** `Diagram m` is a structure with fields `forward`, `backward`, `left`, `right` of type `SetRel (Fin m) (Fin m)`; the product is `Diagram.comp`, the identity is `Diagram.identity m`, and $a\sqsubseteq a'$ is `(a, a') ∈ Diagram.inclusion m`. Words are lists `List (SetRel H H)`, $\pi$ is `relationProduct` (a right fold of `SetRel.comp` starting from `SetRel.id`), and $\pi(w)=\varnothing$ is `¬ (relationProduct w).Nonempty`. The recognition hypothesis is stated for `Diagram.comp (Diagram.comp l (τ w)) r`; since the product is associative this is $l\,\tau(w)\,r$. The words are `List (SetRel (Fin h) (Fin h))` and the unit hypothesis is `τ [] = Diagram.identity m`. The conclusion is `lossBound h ≤ 2 * m` with `lossBound h = 2 ^ ((h - 2) / 127)`, using natural-number subtraction and floor division; since $h\ge2$ the subtraction is not truncated.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean#L90-L110

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.diagram_recognition_lower_bound (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (τ : List (SetRel (Fin h) (Fin h)) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) : lossBound h ≤ 2 * m := by sorry
