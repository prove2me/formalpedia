-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_RectangleFrame_rel_mul
-- name    : OAI.OneWayLiveness.RectangleFrame.rel_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:21:35.583251+00:00
-- url     : https://prove2.me/theorems/169208d6-6ac3-4c3a-ba07-8866d8c91df9
-- title:
--   Rectangle relations multiply by taking the union of their edge sets
-- statement:
--   A rectangle frame $(\ell,r,o)$ in a set $H$, indexed by sets $I$ and $J$, consists of injective maps $\ell\colon I\to H$ and $r\colon J\to H$ and a hub $o\in H$ such that $\ell(i)\neq r(j)$ for all $i\in I$, $j\in J$, and $o$ is neither of the form $\ell(i)$ nor of the form $r(j)$. For $E\subseteq I\times J$, the rectangle relation $R_E$ on $H$ relates $x$ to $y$ if and only if either $x=y\neq o$, or $(x,y)=(\ell(i),r(j))$ for some $(i,j)\in E$. So $R_E$ is the identity off the hub together with one edge from a left point to a right point for each pair in $E$.
--
--   Relations are composed in diagrammatic order: $(x,z)\in RS$ if and only if $(x,y)\in R$ and $(y,z)\in S$ for some $y$. Then for all sets $E,D\subseteq I\times J$,
--
--   $$R_E\,R_D=R_{E\cup D}.$$
--
--   In particular every rectangle relation is idempotent, any two of them commute, and $R_\varnothing$ is the identity relation on $H\setminus\{o\}$. This is the bookkeeping identity used to build the relation $R_E$ of a large edge set one edge at a time, multiplying by the relation of a single new edge.
--
--   **Formalization Note** The frame is `RectangleFrame H I J` and $R_E$ is `F.rel E`. The types $H,I,J$ are arbitrary and $E,D$ are arbitrary (possibly infinite) sets; injectivity of $\ell$ and $r$ is part of the structure but is not needed for this identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Relations.lean#L203-L219

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

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)

theorem OAI.OneWayLiveness.RectangleFrame.rel_mul (E D : Set (I × J)) : F.rel E * F.rel D = F.rel (E ∪ D) := by sorry
