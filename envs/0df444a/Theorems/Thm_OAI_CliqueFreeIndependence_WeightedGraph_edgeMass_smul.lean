-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_smul
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:18:11.674474+00:00
-- url     : https://prove2.me/theorems/752d3c58-6758-4a68-b90f-9190577bdeb9
-- title:
--   The edge mass is quadratic: $E_G(aw)=a^2E_G(w)$
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ and let $w:V\to\mathbb{R}$ be an arbitrary real weight function. Its edge mass is
--   $E_G(w)=\tfrac12\sum_{u\in V}\sum_{v\in V}\mathbf 1[u\sim v]\,w_uw_v=\sum_{\{u,v\}\in E(G)}w_uw_v$. Then for every real number $a$,
--
--   $$
--   E_G(a\,w)=a^{2}\,E_G(w),
--   $$
--
--   where $(a\,w)_v=a\,w_v$.
--
--   So the edge mass is a homogeneous quadratic form in the weights. The identity is used when multiplier vectors are rescaled: for instance $E_G(-w)=E_G(w)$, and multiplying a random multiplier by a constant $k$ multiplies its expected edge mass by $k^{2}$.
--
--   **Formalization Note** The edge mass is `edgeMass G w = crossMass G w univ univ / 2`; no sign condition on $w$ or $a$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean#L22-L34

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u
open Lottery
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_smul (G : SimpleGraph V) (w : V → ℝ) (a : ℝ) :
    edgeMass G (fun v ↦ a*w v) = a^2 * edgeMass G w := by sorry
