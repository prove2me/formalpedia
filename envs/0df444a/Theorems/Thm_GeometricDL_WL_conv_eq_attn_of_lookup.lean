-- Prove2me | Theorems.Thm_GeometricDL_WL_conv_eq_attn_of_lookup
-- name    : GeometricDL.WL.conv_eq_attn_of_lookup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:11.418832+00:00
-- url     : https://prove2.me/theorems/357aad9f-e39a-44f5-8b88-90a78c8905f7
-- title:
--   Convolution ⊆ attention: a look-up table $a(x_u,x_v)=c_{uv}$
-- statement:
--   Let $c:H\times H\to\mathbb R$ be a look-up table of coefficients indexed by the states of the two endpoints. For every finite graph $G=(V,E)$, node states $h:V\to H$, node $u$, message map $\psi$, aggregator $\bigoplus$ and update $\varphi$, the convolutional layer (33) with $c_{uv}=c(h_u,h_v)$ equals the attentional layer (34) with attention $a:=c$:
--
--   $$\varphi\Big(h_u,\bigoplus_{v\in N_u}c(h_u,h_v)\,\psi(h_v)\Big)=\varphi\Big(h_u,\bigoplus_{v\in N_u}a(h_u,h_v)\,\psi(h_v)\Big).$$
--
--   This is the first half of the containment convolution $\subseteq$ attention $\subseteq$ message passing.
--
--   Differences from the source:
--   - reading: "a look-up table a(x_u, x_v) = c_uv" → the convolutional coefficient is c(h_u, h_v), a function of the endpoints' states; reason: a look-up table indexed by (x_u, x_v) can only represent such coefficients; a degree-dependent c_uv = 1/√(d_u d_v) is not one layer of (34) (a featureless node of degree 2 whose neighbours have degree 1 vs 2 gets √2 vs 1, while (34) sees the same features), and such coefficients reach the goal through the milestone on local layers instead
--   - encoding: node features x_u of one layer → the current states h of a stack of layers; reason: Lean convention; the first layer has h = x
--   - encoding: permutation-invariant aggregator ⊕ → an arbitrary function of the multiset of messages, messages in a real vector space; reason: every function of a multiset is permutation-invariant and every permutation-invariant aggregator factors through the multiset
--   - encoding: graph E ⊆ V×V with neighbourhood (11) → a relation E on a finite type, neighbourhood symmetrised, loops allowed; reason: Lean convention; same instances
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, printed p. 79 (PDF p. 83) ("Indeed, attentional GNNs can represent convolutional GNNs by an attention mechanism implemented as a look-up table a(x_u, x_v) = c_uv")

import Mathlib
import Definitions.Def_GeometricDL_WL_convLayer
import Definitions.Def_GeometricDL_WL_attnLayer

namespace GeometricDL.WL

/-- **Containment convolution ⊆ attention: an attention look-up table `a(x_u, x_v) = c_uv`.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
printed p. 79 (PDF p. 83): "One important thing to note is a representational containment between
these approaches: convolution ⊆ attention ⊆ message-passing. Indeed, attentional GNNs can represent
convolutional GNNs by an attention mechanism implemented as a look-up table a(x_u, x_v) = c_uv,"

For every coefficient table `c : H → H → ℝ` indexed by the two endpoints' states, every `ψ`,
aggregator `agg` and update `φ`, every finite graph `(V, E)`, state `h` and node `u`, the
convolutional layer (33) with `c_uv = c(h_u, h_v)` equals the attentional layer (34) with `a := c`.

**Formalization Note.** The look-up table indexes `c_uv` by the endpoint features (states), as the
paper's `a(x_u, x_v) = c_uv` does; a degree-dependent coefficient is not of this form. -/
theorem conv_eq_attn_of_lookup {V : Type*} [Fintype V] {H M A H' : Type*} [AddCommMonoid M]
    [Module ℝ M] (c : H → H → ℝ) (ψ : H → M) (agg : Multiset M → A) (φ : H → A → H')
    (E : V → V → Prop) [DecidableRel E] (h : V → H) (u : V) :
    convLayer (fun hu hv _ _ => c hu hv) ψ agg φ E h u = attnLayer c ψ agg φ E h u := by sorry

end GeometricDL.WL
