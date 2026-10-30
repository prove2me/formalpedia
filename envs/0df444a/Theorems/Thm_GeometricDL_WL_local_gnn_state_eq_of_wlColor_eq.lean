-- Prove2me | Theorems.Thm_GeometricDL_WL_local_gnn_state_eq_of_wlColor_eq
-- name    : GeometricDL.WL.local_gnn_state_eq_of_wlColor_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:24:09.111016+00:00
-- url     : https://prove2.me/theorems/c6322ef9-2542-4171-99c9-99c51548d5f7
-- title:
--   One WL step is an injective local update and refines every local GNN layer
-- statement:
--   Let $G_1=(V_1,E_1,x^{(1)})$ and $G_2=(V_2,E_2,x^{(2)})$ be finite graphs with node features in the same type $F$, let $\mathcal N$ be a local GNN, $L\ge 0$, and $u_1\in V_1$, $u_2\in V_2$. Write $c^{(t)}_u$ for the Weisfeiler–Lehman colour of $u$ after $t$ rounds and $h^{(L)}_u$ for its state after $L$ layers of $\mathcal N$.
--
--   1. (One WL step.) For every local function $\varphi(x_u,X_{N_u})$ that is injective as a function of the pair, $\varphi\big(x^{(1)}_{u_1},X_{N_{u_1}}\big)=\varphi\big(x^{(2)}_{u_2},X_{N_{u_2}}\big)$ if and only if $c^{(1)}_{u_1}(G_1)=c^{(1)}_{u_2}(G_2)$.
--   2. (WL refines every local GNN.) If $u_1$ and $u_2$ receive the same WL colour after $L+1$ rounds, they receive the same state after $L$ layers of $\mathcal N$:
--
--   $$c^{(L+1)}_{u_1}(G_1)=c^{(L+1)}_{u_2}(G_2)\ \Longrightarrow\ h^{(L)}_{u_1}(G_1)=h^{(L)}_{u_2}(G_2).$$
--
--   Clause 2 is the node-level comparison behind the analyses of Morris et al. (2019) and Xu et al. (2018).
--
--   Differences from the source:
--   - generalization: one step of an injective φ(x_u, X_{N_u}) on features in ℝ^s → clause 1 on features of any type F; reason: ℝ^s is a type, and since F is arbitrary clause 1 applies to the input of any layer (in particular to the WL colours of any round)
--   - generalization: the equivalence of one injective step with one WL round → in addition clause 2, L + 1 WL rounds refine L layers of any local GNN (layers that also read neighbour degrees); reason: clause 2 is an extra conclusion used for the goal; one more round than layers is needed there because a local layer reads neighbour degrees, which a WL colour records one round late (a featureless 3-path centre and a triangle node share the round-1 colour, but a layer summing neighbour degrees gives 2 vs 4)
--   - encoding: graph E ⊆ V×V with neighbourhood (11) → a relation E on a finite type, neighbourhood symmetrised, loops allowed; reason: Lean convention; same instances
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §4.1, printed p. 34 (PDF p. 38) ("When φ is injective, it is equivalent to one step of the Weisfeiler-Lehman graph isomorphism test"); node-level step of the analyses cited on printed p. 120 (PDF p. 124)

import Mathlib
import Definitions.Def_GeometricDL_WL_wlColor__89c5bd
import Definitions.Def_GeometricDL_WL_LocalGNN_state

universe u v

namespace GeometricDL.WL

/-- **One WL step is an injective local update, and WL refines every local GNN layer
(node level, across two graphs).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §4.1,
printed p. 34 (PDF p. 38): "When φ is injective, it is equivalent to one step of the
Weisfeiler-Lehman graph isomorphism test, a classical algorithm in graph theory providing a
necessary condition for two graphs to be isomorphic by an iterative color refinement procedure."

For two finite node-featured graphs `(V₁, E₁, x₁)`, `(V₂, E₂, x₂)` with features in the same type
`F`, every local GNN `N`, every depth `L` and nodes `u₁ ∈ V₁`, `u₂ ∈ V₂`:
1. (the page's sentence) for every local function `φ(x_u, X_{N_u})` that is injective (as a
   function of the pair), `u₁` and `u₂` get the same output of `φ` if and only if they get the
   same WL colour after one round;
2. (the step used for the goal) if `u₁` and `u₂` have the same WL colour after `L + 1` rounds,
   they have the same state after `L` layers of `N`.

**Formalization Note.** Clause 1 is stated on arbitrary features `x : V → F`, so it applies to the
input of any layer (in particular to the WL colours of any round). In clause 2 the `L + 1` is
needed: a local layer sees neighbour degrees, which WL colours record one round later
(featureless 3-path centre and triangle node share the round-1 colour, but a layer summing
neighbour degrees gives 2 vs 4). Rounds and layers are 0-based. -/
theorem local_gnn_state_eq_of_wlColor_eq {F : Type u} {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (E₁ : V₁ → V₁ → Prop) [DecidableRel E₁] (x₁ : V₁ → F)
    (E₂ : V₂ → V₂ → Prop) [DecidableRel E₂] (x₂ : V₂ → F)
    (N : LocalGNN.{u, v} F) (L : ℕ) (u₁ : V₁) (u₂ : V₂) :
    (∀ (H : Type v) (φ : F → Multiset F → H), Function.Injective (Function.uncurry φ) →
      (φ (x₁ u₁) ((nbhd E₁ u₁).val.map x₁) = φ (x₂ u₂) ((nbhd E₂ u₂).val.map x₂) ↔
        wlColor E₁ x₁ 1 u₁ = wlColor E₂ x₂ 1 u₂)) ∧
    (wlColor E₁ x₁ (L + 1) u₁ = wlColor E₂ x₂ (L + 1) u₂ →
      N.state E₁ x₁ L u₁ = N.state E₂ x₂ L u₂) := by sorry

end GeometricDL.WL
