-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_word_diagram_order_reversal
-- name    : OAI.TwoWayComplementation.word_diagram_order_reversal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:58:47.802338+00:00
-- url     : https://prove2.me/theorems/9fbb3006-9a7f-4680-b0c4-07bab607e393
-- title:
--   A diagram recognizer of empty relation products reverses inclusion: $\tau(u)\sqsubseteq\tau(v)$ implies $\pi(v)\subseteq\pi(u)$
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
--   For a set $H$, let $\mathrm{Rel}(H)$ be the set of binary relations on $H$, used as an alphabet. For a word $w=X_1X_2\cdots X_k$ over $\mathrm{Rel}(H)$, let $\pi(w)=X_1X_2\cdots X_k$ be the composite relation in path order, with $\pi(\varepsilon)=\mathrm{id}_H$ for the empty word $\varepsilon$; thus $(x,y)\in\pi(w)$ iff there are $x=x_0,x_1,\dots,x_k=y$ with $(x_{i-1},x_i)\in X_i$ for all $i$.
--
--   Let $H$ be a set and $m\in\mathbb{N}$, and let $\tau$ assign a diagram $\tau(w)\in\mathcal{D}_m$ to every word $w$ over $\mathrm{Rel}(H)$ such that $\tau(uv)=\tau(u)\,\tau(v)$ for all words $u,v$. Suppose there are diagrams $l,r\in\mathcal{D}_m$ and labels $a,b\in[m]$ such that for every word $w$
--   $$
--   (a,b)\in F_{l\,\tau(w)\,r}\iff \pi(w)=\varnothing .
--   $$
--   Then for all words $u,v$ over $\mathrm{Rel}(H)$,
--   $$
--   \tau(u)\sqsubseteq\tau(v)\ \Longrightarrow\ \pi(v)\subseteq\pi(u).
--   $$
--
--   The hypothesis says that the boundary labels $a$ and $b$ are connected through $l\,\tau(w)\,r$ exactly when the relation product of $w$ is empty; this is the situation of a two-way automaton recognizing the words with empty product, represented by diagrams. The conclusion says that such a recognizer is order-reversing: more connections in the diagram of a word force fewer pairs in its relation product. This is the key step towards an order-reversing homomorphism from a monoid of diagrams onto the monoid of all relations on $H$.
--
--   **Formalization Note** `Diagram m` is a structure with fields `forward`, `backward`, `left`, `right` of type `SetRel (Fin m) (Fin m)`; the product is `Diagram.comp`, the identity is `Diagram.identity m`, and $a\sqsubseteq a'$ is `(a, a') ∈ Diagram.inclusion m`. Words are lists `List (SetRel H H)`, $\pi$ is `relationProduct` (a right fold of `SetRel.comp` starting from `SetRel.id`), and $\pi(w)=\varnothing$ is `¬ (relationProduct w).Nonempty`. The recognition hypothesis is stated for `Diagram.comp (Diagram.comp l (τ w)) r`; since the product is associative this is $l\,\tau(w)\,r$. No condition on $\tau$ of the empty word is assumed here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean#L10-L34

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

theorem OAI.TwoWayComplementation.word_diagram_order_reversal {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty)
    {u v : List (SetRel H H)} (huv : (τ u, τ v) ∈ Diagram.inclusion m) :
    relationProduct v ⊆ relationProduct u := by sorry
