-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_incoming_good_le
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.incoming_good_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:45:57.429112+00:00
-- url     : https://prove2.me/theorems/9bdba34f-dc60-45fe-9f6f-fd40ca63125d
-- title:
--   One lazy step of the smoothed local walk rarely leaves a neighbourhood enlargement
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ and $w:V\to\mathbb{R}$ a weight with $w(u)>0$ for all $u$. For $S\subseteq V$ write $w(S)=\sum_{s\in S}w(s)$; let $N(u)$ be the neighbourhood of $u$ and $W(u,v)=w(N(u)\cap N(v))$. Let $\vec E(G)$ be the set of oriented edges $(u,v)$ with $u\sim v$, and for $e=(u,v)$ write $e^{-}=u$, $e^{+}=v$. The *local walk* is the kernel $T$ on $\vec E(G)$ with $T(e,f)=w(f^{+})/W(e^{-},e^{+})$ if $f^{-}=e^{-}$ and $e^{+}\sim f^{+}$, and $T(e,f)=0$ otherwise; its *lazy version* is $L=\tfrac12(\mathrm{Id}+T)$, and the *smoothed kernels* are the matrix products $S_n=T\,L^{n}$ for $n\in\mathbb{N}$. For $u\in V$ and $B\subseteq V$ put $\operatorname{lift}_u(B)=\{f\in\vec E(G):f^{-}=u,\ f^{+}\in B\}$, and for $t\in\mathbb{R}$ and $A\subseteq V$ define the *enlargement* $A^{+}_t=A\cup\{y\in V:\ w(A\cap N(y))\ge t\}$.
--
--   Let $x>0$ and assume $W(u,v)\ge1/x$ for every edge $uv$ of $G$. Let $t\ge0$, $n\in\mathbb{N}$, $e\in\vec E(G)$ with first endpoint $u=e^{-}$, and $A\subseteq V$. Then
--
--   $$
--   \sum_{y\in\vec E(G)\setminus\operatorname{lift}_u(A^{+}_t)}\ \sum_{z\in\operatorname{lift}_u(A)}S_n(e,z)\,L(z,y)\;\le\;x^{2}\,t\,w\big(N(u)\big).
--   $$
--
--   The left side is the probability that the walk started at $e$ is, after the smoothed kernel $S_n$, at an oriented edge from $u$ into $A$, and that the following lazy step takes it to an oriented edge outside $\operatorname{lift}_u(A^{+}_t)$. Because a step can only move the second endpoint to a neighbour, and every vertex outside $A^{+}_t$ sees less than $t$ of the weight of $A$, this probability is small. Combined with the two-step leakage inequality for stochastic kernels, it shows by induction on $n$ that the smoothed walk from $e$ stays inside the lift of the $n$-fold enlargement of $N(e^{+})$, up to an error at most $n\,x^{2}t\max_{v}w(N(v))$.
--
--   **Formalization Note** $e^{-}$, $e^{+}$ are `e.src`, `e.dst`; $L$ is `lazy (transition G w)`, $S_n$ is `smoothed (transition G w) n`, $\operatorname{lift}_u(B)$ is `liftSet u B`, $A^{+}_t$ is `enlarge G w t A` and $w(N(u))$ is `neighborMass G w u`. The outer sum runs over the complement of `liftSet` in the finite type `EdgeState G`, so it also includes oriented edges whose first endpoint differs from $u$; these contribute $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/WalkEntropy.lean#L74-L139

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.incoming_good_le (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) (A : Finset V) :
    (∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
      ∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
      x ^ 2 * t * neighborMass G w e.src := by sorry
