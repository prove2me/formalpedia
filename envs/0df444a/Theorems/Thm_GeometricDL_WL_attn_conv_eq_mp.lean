-- Prove2me | Theorems.Thm_GeometricDL_WL_attn_conv_eq_mp
-- name    : GeometricDL.WL.attn_conv_eq_mp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:48.286227+00:00
-- url     : https://prove2.me/theorems/366921e1-ac81-467e-80d1-2eb2d9a7c5b8
-- title:
--   Attention, convolution ⊆ message passing
-- statement:
--   For every finite graph $G=(V,E)$, node states $h:V\to H$, node $u$, message map $\psi:H\to M$ into a real vector space, aggregator $\bigoplus$, update $\varphi$, attention $a:H\times H\to\mathbb R$ and look-up coefficient $c:H\times H\to\mathbb R$:
--
--   1. the attentional layer (34) is the message-passing layer (35) with message $\psi'(h_u,h_v)=a(h_u,h_v)\,\psi(h_v)$;
--   2. the convolutional layer (33) with $c_{uv}=c(h_u,h_v)$ is the message-passing layer (35) with message $\psi'(h_u,h_v)=c(h_u,h_v)\,\psi(h_v)$.
--
--   $$\varphi\Big(h_u,\bigoplus_{v\in N_u}a(h_u,h_v)\psi(h_v)\Big)=\varphi\Big(h_u,\bigoplus_{v\in N_u}\psi'(h_u,h_v)\Big).$$
--
--   Both are special cases of message passing in which the message depends on the sender's features only through $\psi(h_v)$. Together with the previous milestone this is the containment convolution $\subseteq$ attention $\subseteq$ message passing.
--
--   Differences from the source:
--   - reading: ψ(x_u, x_v) = c_uv ψ(x_v) for convolutional GNNs → c_uv = c(h_u, h_v), a function of the endpoints' states; reason: as in the previous milestone, a message ψ(x_u, x_v) can only carry a coefficient that is a function of (x_u, x_v); degree-dependent coefficients reach the goal through the local-layer milestone
--   - encoding: node features x_u of one layer → the current states h of a stack of layers; reason: Lean convention; the first layer has h = x
--   - encoding: permutation-invariant aggregator ⊕ → an arbitrary function of the multiset of messages, messages in a real vector space; reason: every function of a multiset is permutation-invariant and every permutation-invariant aggregator factors through the multiset
--   - encoding: graph E ⊆ V×V with neighbourhood (11) → a relation E on a finite type, neighbourhood symmetrised, loops allowed; reason: Lean convention; same instances
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, printed pp. 79–80 (PDF pp. 83–84) ("both convolutional and attentional GNNs are special cases of message-passing where the messages are only the sender nodes' features")

import Mathlib
import Definitions.Def_GeometricDL_WL_convLayer
import Definitions.Def_GeometricDL_WL_attnLayer
import Definitions.Def_GeometricDL_WL_mpLayer

namespace GeometricDL.WL

/-- **Containment attention, convolution ⊆ message passing.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
printed pp. 79–80 (PDF pp. 83–84): "and both convolutional and attentional GNNs are special cases
of message-passing where the messages are only the sender nodes' features: ψ(x_u, x_v) = c_uv ψ(x_v)
for convolutional GNNs and ψ(x_u, x_v) = a(x_u, x_v)ψ(x_v) for attentional GNNs."

For every finite graph `(V, E)`, state `h`, node `u`, `ψ`, aggregator `agg` and update `φ`:
1. the attentional layer (34) with attention `a` equals the message-passing layer (35) with
   message `ψ'(h_u, h_v) = a(h_u, h_v) • ψ(h_v)`;
2. the convolutional layer (33) with look-up coefficient `c_uv = c(h_u, h_v)` equals the
   message-passing layer (35) with message `ψ'(h_u, h_v) = c(h_u, h_v) • ψ(h_v)`.

**Formalization Note.** As in `conv_eq_attn_of_lookup`, the convolutional coefficient is indexed by
the endpoints' states. -/
theorem attn_conv_eq_mp {V : Type*} [Fintype V] {H M A H' : Type*} [AddCommMonoid M]
    [Module ℝ M] (a c : H → H → ℝ) (ψ : H → M) (agg : Multiset M → A) (φ : H → A → H')
    (E : V → V → Prop) [DecidableRel E] (h : V → H) (u : V) :
    attnLayer a ψ agg φ E h u = mpLayer (fun hu hv => a hu hv • ψ hv) agg φ E h u ∧
      convLayer (fun hu hv _ _ => c hu hv) ψ agg φ E h u =
        mpLayer (fun hu hv => c hu hv • ψ hv) agg φ E h u := by sorry

end GeometricDL.WL
