-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_PathNFA_product_path
-- name    : OAI.OneWayLiveness.PathNFA.product_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:31:10.86013+00:00
-- url     : https://prove2.me/theorems/ec1b5893-5302-4465-96d8-40c187d40893
-- title:
--   A pair lies in a product of relations iff a path threads through the factors
-- statement:
--   Let $H$ be any set and let $R_1,\dots,R_n$ be binary relations on $H$, composed in diagrammatic order, so that $(x,z)\in RS$ if and only if $(x,y)\in R$ and $(y,z)\in S$ for some $y$; the empty product is the identity relation. For all $a,b\in H$,
--
--   $$(a,b)\in R_1R_2\cdots R_n\iff \exists\,p\colon\mathbb N\to H\ \text{ with }\ p(0)=a,\ \ p(n)=b,\ \ (p(i),p(i+1))\in R_{i+1}\ \text{ for all } 0\le i<n .$$
--
--   Thus membership in an iterated relational product is the existence of a path $a=p(0),p(1),\dots,p(n)=b$ whose $k$-th step is allowed by the $k$-th relation; for $n=0$ the statement says $(a,b)\in\Delta_H$ iff $a=b$. This is how the correctness of the path automaton for one-way liveness is established: an accepting run guesses such a path letter by letter.
--
--   **Formalization Note** The relations form a list `w : List (BRel H)` and the product is `w.prod` in the monoid `BRel H`; the path is a function on all of $\mathbb N$ whose values after $n$ are irrelevant, and the factor $R_{i+1}$ is the zero-indexed entry `w[i]`. No finiteness of $H$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/PathNFA.lean#L90-L116

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.PathNFA
variable {H : Type}

theorem OAI.OneWayLiveness.PathNFA.product_path (w : List (BRel H)) (a b : H) :
    w.prod.holds a b ↔ ∃ p : ℕ → H, p 0 = a ∧ p w.length = b ∧
      ∀ i (hi : i < w.length), w[i].holds (p i) (p (i+1)) := by sorry
