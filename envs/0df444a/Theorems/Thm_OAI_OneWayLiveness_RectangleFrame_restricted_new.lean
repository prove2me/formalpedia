-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_RectangleFrame_restricted_new
-- name    : OAI.OneWayLiveness.RectangleFrame.restricted_new
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:23:39.540241+00:00
-- url     : https://prove2.me/theorems/f6fd82a2-e2bc-4d29-a3d3-27caed6930eb
-- title:
--   On a set missing all old edges, adding one rectangle edge restricts to the identity plus that edge
-- statement:
--   A rectangle frame $(\ell,r,o)$ in a set $H$, indexed by sets $I$ and $J$, consists of injective maps $\ell\colon I\to H$ and $r\colon J\to H$ and a hub $o\in H$ such that $\ell(i)\neq r(j)$ for all $i\in I$, $j\in J$, and $o$ is neither of the form $\ell(i)$ nor of the form $r(j)$. For $E\subseteq I\times J$, the rectangle relation $R_E$ on $H$ relates $x$ to $y$ if and only if either $x=y\neq o$, or $(x,y)=(\ell(i),r(j))$ for some $(i,j)\in E$. So $R_E$ is the identity off the hub together with one edge from a left point to a right point for each pair in $E$.
--
--   Let $E\subseteq I\times J$ and $K\subseteq H$ be sets such that the hub is not in $K$, and no pair of $E$ has both endpoints in $K$: for every $(i',j')\in E$, $\ell(i')\notin K$ or $r(j')\notin K$. Let $(i,j)\in I\times J$ with $\ell(i)\in K$ and $r(j)\in K$. Then for all $x,y\in K$,
--
--   $$(x,y)\in R_{E\cup\{(i,j)\}}\iff x=y\ \text{ or }\ (x,y)=(\ell(i),r(j)).$$
--
--   In other words, the restriction of $R_{E\cup\{(i,j)\}}$ to $K$ is the relation $\Delta_K\cup\{(\ell(i),r(j))\}$ on $K$: the identity with exactly one extra pair. (The hypotheses force $(i,j)\notin E$.) In the exponential rank-loss argument $K$ is the set retained after deleting all other frame points, and this lemma shows that the newest edge is the only one visible there, which is exactly the shape required by the induction hypothesis.
--
--   **Formalization Note** The right-hand side is `BRel.addEdge u v` on the subtype $K$, where $u$ and $v$ are $\ell(i)$ and $r(j)$ viewed as elements of $K$; $E\cup\{(i,j)\}$ is `insert (i,j) E`. The sets $E$ and $K$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Relations.lean#L255-L272

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

theorem OAI.OneWayLiveness.RectangleFrame.restricted_new (E : Set (I × J)) (K : Set H)
    (hK : ∀ x ∈ K, x ≠ F.hub)
    (hE : ∀ p ∈ E, F.left p.1 ∉ K ∨ F.right p.2 ∉ K)
    (i : I) (j : J) (hi : F.left i ∈ K) (hj : F.right j ∈ K) :
    let u : K := ⟨F.left i,hi⟩
    let v : K := ⟨F.right j,hj⟩
    ∀ x y : K, (F.rel (insert (i,j) E)).holds x.val y.val ↔ (BRel.addEdge u v).holds x y := by sorry
