-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Diamond_hasDistortion_iff_all_pairs
-- name    : OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:12:54.267984+00:00
-- url     : https://prove2.me/theorems/80a9ddd5-d968-4253-b2bb-51d8653ee347
-- title:
--   The condition $D\ge1$ in the diamond-graph distortion hypothesis is automatic
-- statement:
--   The countably branching diamond graphs $G_0,G_1,\dots$ are built together with their edge sets $E_n$ and vertex sets $V_n$. The graph $G_0$ has the two vertices $V_0=\{0,1\}$ and one edge, $E_0=\{\ast\}$, which runs from $a_\ast=0$ to $b_\ast=1$. Given stage $n$, put
--   $$E_{n+1}=E_n\times\mathbb{N}\times\{0,1\},\qquad V_{n+1}=V_n\sqcup(E_n\times\mathbb{N}),$$
--   so that $V_{n+1}$ consists of the *old* vertices of $V_n$ together with a *midpoint* $m_{e,i}$ for every edge $e\in E_n$ and every $i\in\mathbb{N}$. If $e\in E_n$ runs from $a_e$ to $b_e$, then the edge $(e,i,0)\in E_{n+1}$ runs from $a_e$ to $m_{e,i}$ and the edge $(e,i,1)$ runs from $m_{e,i}$ to $b_e$. Two distinct vertices $u,v\in V_n$ are adjacent in $G_n$ when some edge of $E_n$ runs from $u$ to $v$ or from $v$ to $u$. Thus $G_{n+1}$ arises from $G_n$ by replacing every edge by countably many paths of length two between its endpoints, each through its own new midpoint. Write $d_{G_n}(u,v)$ for the shortest-path distance (number of edges) in $G_n$ and $d_n(u,v)=d_{G_n}(u,v)/2^n$ for the normalized distance, in which every edge of $G_n$ has length $2^{-n}$.
--
--   Let $X$ be a normed abelian group, $k\in\mathbb{N}$, $f\colon V_k\to X$ and $D,s\in\mathbb{R}$. Say that $f$ *has distortion $D$ at scale $s$* if $D\ge1$, $s>0$, and
--   $$s\,d_k(u,v)\le\|f(u)-f(v)\|\le D\,s\,d_k(u,v)\qquad\text{for all }u,v\in V_k .$$
--
--   **Theorem.** $f$ has distortion $D$ at scale $s$ if and only if $s>0$ and the two-sided inequality above holds for all $u,v\in V_k$.
--
--   So the conventional requirement $D\ge1$ adds no hypothesis: it follows from the all-pairs inequalities themselves. This allows a distortion lower bound stated for maps with distortion $D$ to be applied to maps that are only known to satisfy the two-sided all-pairs inequalities with a positive scale.
--
--   **Formalization Note** The types are `Diamond.Edge n` and `Diamond.Vertex n`, the endpoints of an edge are `Diamond.endpoint n e false` (start) and `Diamond.endpoint n e true` (end), old vertices of stage $n+1$ are `Sum.inl u` and midpoints are `Sum.inr (e, i)`, and $G_n$ is `Diamond.graph n`, built with `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops. The predicate is `Diamond.HasDistortion k f D s`; here $X$ only needs to be a `NormedAddCommGroup`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Descent.lean#L85-L101

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds
import Definitions.Def_OAI_Analysis_DiamondDistortion_SignCube
import Definitions.Def_OAI_Analysis_DiamondDistortion_HeadProjections

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped ENNReal
variable {X : Type*} [NormedAddCommGroup X]

theorem OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs {k : ℕ} (f : Vertex k → X) (D s : ℝ) :
    HasDistortion k f D s ↔ 0 < s ∧ ∀ u v,
      s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ D*s*distance k u v := by sorry
