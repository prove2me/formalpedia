-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Diamond_squared_stretch_loss
-- name    : OAI.DiamondDistortion.Diamond.squared_stretch_loss
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:10:21.596233+00:00
-- url     : https://prove2.me/theorems/b83d901b-7b50-43a7-a8b4-705912db7380
-- title:
--   Squared stretch loss for maps of diamond graphs into spaces with the quadratic lens property
-- statement:
--   The countably branching diamond graphs $G_0,G_1,\dots$ are built together with their edge sets $E_n$ and vertex sets $V_n$. The graph $G_0$ has the two vertices $V_0=\{0,1\}$ and one edge, $E_0=\{\ast\}$, which runs from $a_\ast=0$ to $b_\ast=1$. Given stage $n$, put
--   $$E_{n+1}=E_n\times\mathbb{N}\times\{0,1\},\qquad V_{n+1}=V_n\sqcup(E_n\times\mathbb{N}),$$
--   so that $V_{n+1}$ consists of the *old* vertices of $V_n$ together with a *midpoint* $m_{e,i}$ for every edge $e\in E_n$ and every $i\in\mathbb{N}$. If $e\in E_n$ runs from $a_e$ to $b_e$, then the edge $(e,i,0)\in E_{n+1}$ runs from $a_e$ to $m_{e,i}$ and the edge $(e,i,1)$ runs from $m_{e,i}$ to $b_e$. Two distinct vertices $u,v\in V_n$ are adjacent in $G_n$ when some edge of $E_n$ runs from $u$ to $v$ or from $v$ to $u$. Thus $G_{n+1}$ arises from $G_n$ by replacing every edge by countably many paths of length two between its endpoints, each through its own new midpoint. Each $V_n$ is regarded as a subset of $V_{n+1}$. Write $d_{G_n}(u,v)$ for the shortest-path distance (number of edges) in $G_n$ and $d_n(u,v)=d_{G_n}(u,v)/2^n$ for the normalized distance, in which every edge of $G_n$ has length $2^{-n}$.
--
--   Let $X$ be a real normed space. For $f\colon V_k\to X$ and an edge $e\in E_k$ the *slope* of $f$ along $e$ is
--   $$\sigma_f(e)=2^k\bigl(f(b_e)-f(a_e)\bigr),$$
--   the increment of $f$ along $e$ divided by the length $2^{-k}$ of $e$. The space $X$ has the *quadratic lens property* if for every $x\in X$, every sequence $(z_i)_{i\in\mathbb{N}}$ in $X$ and all real $R\ge0$, $\varepsilon>0$ such that $\|x+z_i\|\le R$ and $\|x-z_i\|\le R$ for all $i$ and $\|z_i-z_j\|\ge\varepsilon$ for all $i\ne j$, one has $\|x\|^2+\varepsilon^2/16\le R^2$.
--
--   **Theorem.** Let $X$ be a real normed space with the quadratic lens property, let $k\in\mathbb{N}$, $f\colon V_k\to X$, and let $s,B\in\mathbb{R}$ with $s>0$. Suppose that
--   - $s\,d_k(u,v)\le\|f(u)-f(v)\|$ for all $u,v\in V_k$, and
--   - $\|\sigma_f(e)\|^2\le B$ for every edge $e\in E_k$.
--
--   Then
--   $$s^2\Bigl(1+\frac k4\Bigr)\le B .$$
--
--   Read from stage $k$ back to stage $0$, each subdivision step lowers a common bound on the squared slopes by $s^2/4$; the argument never has to select an edge or a child of maximal slope. If $f$ satisfies $s\,d_k\le\|f(u)-f(v)\|\le Ds\,d_k$, then every slope has norm at most $Ds$, and the theorem with $B=(Ds)^2$ gives the distortion lower bound $D^2\ge1+k/4$.
--
--   **Formalization Note** The types are `Diamond.Edge n` and `Diamond.Vertex n`, the endpoints of an edge are `Diamond.endpoint n e false` (start) and `Diamond.endpoint n e true` (end), old vertices of stage $n+1$ are `Sum.inl u` and midpoints are `Sum.inr (e, i)`, and $G_n$ is `Diamond.graph n`, built with `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops. The slope is `Diamond.slope f e`, the normalized distance is `Diamond.distance k`, and the quadratic lens property is `Diamond.QuadraticLens X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean#L275-L311

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
universe u v
open scoped BigOperators Classical Topology
open Set
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.DiamondDistortion.Diamond.squared_stretch_loss (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    {s B : ℝ} (hs : 0 < s)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖^2 ≤ B) : s^2*(1+(k:ℝ)/4) ≤ B := by sorry
