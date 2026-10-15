-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_diagram_relation_image
-- name    : OAI.TwoWayComplementation.diagram_relation_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:59:30.242762+00:00
-- url     : https://prove2.me/theorems/09b09e85-8ea3-443b-a557-0c97e5d9fdc8
-- title:
--   A diagram recognizer of empty relation products yields an order-reversing homomorphism onto the relation monoid
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
--   For a set $H$, let $\mathrm{Rel}(H)$ be the set of binary relations on $H$, used as an alphabet. For a word $w=X_1X_2\cdots X_k$ over $\mathrm{Rel}(H)$, let $\pi(w)=X_1X_2\cdots X_k$ be the composite relation in path order, with $\pi(\varepsilon)=\mathrm{id}_H$ for the empty word $\varepsilon$; thus $(x,y)\in\pi(w)$ iff there are $x=x_0,x_1,\dots,x_k=y$ with $(x_{i-1},x_i)\in X_i$ for all $i$. Let $\mathcal{R}(H)$ be the monoid of all binary relations on $H$ with composition in path order and identity $\mathrm{id}_H$.
--
--   Let $H$ be a set and $m\in\mathbb{N}$, and let $\tau$ assign a diagram $\tau(w)\in\mathcal{D}_m$ to every word $w$ over $\mathrm{Rel}(H)$ such that $\tau(\varepsilon)=\mathbf{1}$ and $\tau(uv)=\tau(u)\,\tau(v)$ for all words $u,v$. Suppose there are diagrams $l,r\in\mathcal{D}_m$ and labels $a,b\in[m]$ such that for every word $w$
--   $$
--   (a,b)\in F_{l\,\tau(w)\,r}\iff \pi(w)=\varnothing .
--   $$
--   Then there exist a submonoid $S$ of $\mathcal{D}_m$ and a monoid homomorphism $\varphi:S\to\mathcal{R}(H)$ that is surjective and reverses inclusion:
--   $$
--   \varphi(S)=\mathcal{R}(H)\qquad\text{and}\qquad z\sqsubseteq z'\ \Longrightarrow\ \varphi(z')\subseteq\varphi(z)\quad\text{for all } z,z'\in S .
--   $$
--
--   Thus a monoid of diagrams on $m$ labels maps onto the full relation monoid of $H$ by an order-reversing homomorphism whenever the words with empty relation product are recognized through diagrams on $m$ labels. Such an order-reversing image is the input of the image bound, which forces $m$ to be exponentially large in $|H|$.
--
--   **Formalization Note** `Diagram m` is a structure with fields `forward`, `backward`, `left`, `right` of type `SetRel (Fin m) (Fin m)`; the product is `Diagram.comp`, the identity is `Diagram.identity m`, and $a\sqsubseteq a'$ is `(a, a') ∈ Diagram.inclusion m`. Words are lists `List (SetRel H H)`, $\pi$ is `relationProduct` (a right fold of `SetRel.comp` starting from `SetRel.id`), and $\pi(w)=\varnothing$ is `¬ (relationProduct w).Nonempty`. The recognition hypothesis is stated for `Diagram.comp (Diagram.comp l (τ w)) r`; since the product is associative this is $l\,\tau(w)\,r$. The unit hypothesis is `τ [] = Diagram.identity m`. $\mathcal{R}(H)$ is `RelationMonoid H`, the opposite of the endomorphism monoid of $H$ in Mathlib's category of relations, chosen so that its product is composition in path order; `toRel` gives the underlying relation. $S$ is a `Submonoid (Diagram m)` for the monoid structure on `Diagram m` given by `comp` and `identity`, and $\varphi$ is a `MonoidHom`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean#L36-L88

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

theorem OAI.TwoWayComplementation.diagram_relation_image {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) :
    ∃ S : Submonoid (Diagram m), ∃ φ : S →* RelationMonoid H,
      Function.Surjective φ ∧
      (∀ z w : S, (z.val, w.val) ∈ Diagram.inclusion m → (φ w).toRel ⊆ (φ z).toRel) := by sorry
