-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_divergence
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.optimizer_divergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:17:27.769683+00:00
-- url     : https://prove2.me/theorems/99f9846c-2150-4f57-b195-33abaeea44ae
-- title:
--   Exact expansion of the potential around an optimizer as a divergence plus an edge term
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ (no loops, so $u\sim v$ implies $u\ne v$), and write $N(v)$ for the set of neighbours of a vertex $v$. For a weight function $w:V\to\mathbb{R}$ and $S\subseteq V$ put $w(S)=\sum_{v\in S}w_v$, and let $N_v(w)=w(N(v))=\sum_{u\sim v}w_u$ be the neighbour mass of $v$. The edge mass of $w$ is
--   $E_G(w)=\tfrac12\sum_{u\in V}\sum_{v\in V}\mathbf 1[u\sim v]\,w_uw_v=\sum_{\{u,v\}\in E(G)}w_uw_v,$
--   and the potential of $w$ is
--   $\Phi_G(w)=\sum_{v\in V}\varphi(w_v)-E_G(w)$, where $\varphi(t)=t\,(1-\log t)$ ($\log$ is the natural logarithm) and $\varphi(0)=0$. A weight function $w$ is called an *optimizer* for $G$ if $w_v\ge0$ for every $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q:V\to\mathbb{R}$ with $q_v\ge0$ for all $v$; that is, $w$ maximizes $\Phi_G$ over the nonnegative orthant.
--
--   Let $w$ be an optimizer for $G$ and let $q:V\to\mathbb{R}$ satisfy $q_v\ge0$ for all $v$. Then $\Phi_G(w)-\Phi_G(q)\ge0$, and
--
--   $$
--   \Phi_G(w)-\Phi_G(q)=\sum_{v\in V}\Bigl(q_v\log\frac{q_v}{w_v}-q_v+w_v\Bigr)+E_G(q-w).
--   $$
--
--   Here a summand with $q_v=0$ is read as $w_v$ (convention $0\cdot\log 0=0$), and $E_G(q-w)$ is the edge mass of the difference $q-w$, which may take both signs. Each vertex summand is a term of the generalized Kullback–Leibler divergence between the nonnegative vectors $q$ and $w$, so the identity splits the loss of potential of any competitor $q$ into a divergence part and a quadratic edge part. It is the tool used to compute the exact cost of deleting vertex sets from an optimizer.
--
--   **Formalization Note** The edge mass is `edgeMass G w = crossMass G w univ univ / 2`, the vertex summand is `vertexPotential t = t * (1 - Real.log t)` (Lean's convention $\log 0=0$ makes it vanish at $t=0$), the potential is `potential G w`, and `IsOptimizer G w` is the maximality property described above, quantified over all nonnegative real-valued functions on $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Optimizer.lean#L218-L244

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.optimizer_divergence {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    0 ≤ potential G w - potential G q ∧
      potential G w - potential G q =
        (∑ v, (q v * Real.log (q v / w v) - q v + w v)) + edgeMass G (q-w) := by sorry
