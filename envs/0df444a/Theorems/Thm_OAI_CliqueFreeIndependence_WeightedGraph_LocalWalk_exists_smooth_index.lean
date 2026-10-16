-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_exists_smooth_index
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.exists_smooth_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:47:14.001785+00:00
-- url     : https://prove2.me/theorems/ae2fb21e-4745-41cf-91fa-9b3d81a9c63b
-- title:
--   A smoothing time for the local walk with low average entropy and small row distance
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with at least one edge, and let $w:V\to\mathbb{R}$ satisfy $w(u)>0$ for all $u$. We use the following notation.
--
--   - $w(S)=\sum_{s\in S}w(s)$ for $S\subseteq V$; $N(u)$ is the neighbourhood of $u$; $W(u,v)=w(N(u)\cap N(v))$.
--   - For $A,B\subseteq V$ the cross mass is $e_w(A,B)=\sum_{a\in A}\sum_{b\in B}\mathbf 1[a\sim b]\,w(a)\,w(b)$, and for real $\lambda$ and $s\ge0$ let $g_\lambda(s)=s\,\big(\lambda+\max\{0,\log(1/s)\}\big)$, with $g_\lambda(0)=0$. The weighted graph satisfies the *cross bound with constant $C$* if $e_w(A,B)\le C\,g_\lambda(w(A))$ for every real $\lambda\ge1$ and all (possibly overlapping) $A,B\subseteq V$ with $w(A)\le e^{\lambda}$ and $w(B)\le e^{\lambda}$.
--   - $\vec E(G)$ is the set of oriented edges $e=(e^{-},e^{+})$ with $e^{-}\sim e^{+}$. The local walk is $T(e,f)=w(f^{+})/W(e^{-},e^{+})$ if $f^{-}=e^{-}$ and $e^{+}\sim f^{+}$, and $0$ otherwise; $L=\tfrac12(\mathrm{Id}+T)$ is its lazy version and $S_j=T\,L^{j}$ ($j\in\mathbb{N}$) are the smoothed kernels. The edge law is $\pi(e)=w(e^{-})w(e^{+})W(e^{-},e^{+})/Z$ with $Z=\sum_{f\in\vec E(G)}w(f^{-})w(f^{+})W(f^{-},f^{+})$.
--   - For a probability vector $p$ on $\vec E(G)$, $H(p)=\sum_fp_f\log\big(w(f^{+})/p_f\big)$ (terms with $p_f=0$ vanish), and $\overline H(S_j)=\sum_e\pi(e)\,H\big(S_j(e,\cdot)\big)$. With $d_{\mathrm{TV}}(p,q)=\tfrac12\sum_f|p_f-q_f|$, the row distance at time $j$ is $\rho(j)=\sum_e\pi(e)\sum_fT(e,f)\,d_{\mathrm{TV}}\big(S_j(e,\cdot),S_j(f,\cdot)\big)$.
--   - $\kappa(C)=10+42C^{2}+2C$ and $\sigma(C)=2\sqrt{\kappa(C)+1}$.
--
--   Assume that $C\ge1$, that the cross bound with constant $C$ holds, that $x\ge32$, that $W(u,v)\ge1/x$ for every edge $uv$, and that $w(N(u))\le e^{x}$ for every vertex $u$. Then there is a natural number $j<\lceil x\rceil$ such that
--
--   $$
--   \overline H(S_j)\le\kappa(C)\,\log x\qquad\text{and}\qquad\rho(j)\le\sigma(C)\sqrt{\frac{\log x}{x}} .
--   $$
--
--   The theorem finds a time at which the smoothed local walk is simultaneously concentrated, with average row entropy $O_C(\log x)$ instead of the trivial bound $x$ implied by $w(N(u))\le e^{x}$, and nearly invariant under one more step of the walk, since rows of $T$-neighbouring states are on average close in total variation. In the weighted vertex-splitting step of the independence-number argument, splitting vertices according to $S_j$ loses a fraction of the triangle mass that is controlled by these two quantities.
--
--   **Formalization Note** $\pi$ is `law G w`, $H$ is `entropy (vertexWeight G w)`, $\overline H(S_j)$ is `avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) j)`, $\rho$ is `rowDistance`, $\kappa$ and $\sigma$ are `entropyConstant` and `smoothingConstant`, and the cross bound is `CrossBound G w C` (with $g_\lambda$ = `growth`, where Lean's $1/0=0$, $\log 0=0$ give $g_\lambda(0)=0$). $\lceil x\rceil$ is the natural-number ceiling `⌈x⌉₊`. The existence of an edge is the instance `[Nonempty (EdgeState G)]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/WalkEntropy.lean#L337-L378

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}

theorem OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.exists_smooth_index [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ j < ⌈x⌉₊,
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) j) ≤
        entropyConstant C * Real.log x ∧
      rowDistance (G := G) (w := w) j ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by sorry
