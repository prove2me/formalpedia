-- Prove2me | Theorems.Thm_GeometricDL_WL_flavours_are_local
-- name    : GeometricDL.WL.flavours_are_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:25.830801+00:00
-- url     : https://prove2.me/theorems/d8a04938-986c-4995-a08a-ce76c6f140be
-- title:
--   Every flavour is a shared local function $\varphi(x_u,X_{N_u})$ (corrected: (33) also sees neighbour degrees)
-- statement:
--   Fix the parameters of each flavour. Then there are update functions $\Phi$, not depending on the graph, such that for every finite graph $G=(V,E)$, node states $h:V\to H$ and node $u$, with $X_{N_u}=\{\!\{h_v:v\in N_u\}\!\}$:
--
--   1. the convolutional layer (33) with coefficient $c_{uv}=\kappa(h_u,h_v,|N_u|,|N_v|)$ satisfies
--   $$h'_u=\Phi_{\mathrm{conv}}\Big(h_u,\ \{\!\{(h_v,|N_v|):v\in N_u\}\!\}\Big);$$
--   2. the attentional layer (34) satisfies $h'_u=\Phi_{\mathrm{att}}(h_u,X_{N_u})$;
--   3. the message-passing layer (35) satisfies $h'_u=\Phi_{\mathrm{mp}}(h_u,X_{N_u})$.
--
--   So every layer of the three flavours is a shared, permutation-invariant local function of a node's state and its neighbourhood, and every stack of such layers is a local GNN.
--
--   Differences from the source:
--   - correction: (33) is a function φ(x_u, X_{N_u}) with c_uv "a constant that often directly depends on the entries in A" → c_uv = κ(h_u, h_v, |N_u|, |N_v|), and the local function also reads each neighbour's degree |N_v|; reason: with c_uv = 1/√(d_u d_v) (Kipf–Welling, cited for (33)), ψ ≡ 1, ⊕ = Σ, φ(x, z) = z, a featureless node of degree 2 with two degree-1 neighbours gets √2 and one with two degree-2 neighbours gets 1, although both have X_{N_u} = {{0, 0}}; with c_uv = number of triangles of A, no local function exists at all (6-cycle vs two triangles)
--   - encoding: node features x_u of one layer → the current states h of a stack of layers; reason: Lean convention; the first layer has h = x
--   - encoding: permutation-invariant aggregator ⊕ → an arbitrary function of the multiset of messages, messages in a real vector space; reason: every function of a multiset is permutation-invariant and every permutation-invariant aggregator factors through the multiset
--   - encoding: graph E ⊆ V×V with neighbourhood (11) → a relation E on a finite type, neighbourhood symmetrised, loops allowed; reason: Lean convention; same instances
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, printed p. 78 (PDF p. 82) ("We will study GNN architectures that are permutation equivariant functions F(X, A) constructed by applying shared permutation invariant functions φ(x_u, X_{N_u}) over local neighbourhoods"); flavours (33)–(35), printed p. 79 (PDF p. 83); eq. (13), printed p. 34 (PDF p. 38)

import Mathlib
import Definitions.Def_GeometricDL_WL_convLayer
import Definitions.Def_GeometricDL_WL_attnLayer
import Definitions.Def_GeometricDL_WL_mpLayer

universe w

namespace GeometricDL.WL

/-- **Every layer of the three flavours is a shared local function `φ(x_u, X_{N_u})`.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
printed p. 78 (PDF p. 82): "We will study GNN architectures that are permutation equivariant
functions F(X, A) constructed by applying shared permutation invariant functions φ(x_u, X_{N_u})
over local neighbourhoods."; flavours (33)–(35), printed p. 79 (PDF p. 83); eq. (13), p. 34.

For each flavour and each choice of its parameters there is one function `Φ`, independent of the
graph, such that for every finite graph `(V, E)` (with `V : Type w`), every state `h : V → H` and
every node `u`, the layer's output at `u` is a function of `h u` and the neighbourhood multiset
`X_{N_u} = {{ h v : v ∈ N_u }}` (12):
1. the convolutional layer (33) with coefficient `κ(h_u, h_v, |N_u|, |N_v|)`: its output is
   `Φ (h u) {{ (h v, |N_v|) : v ∈ N_u }}` (each neighbour's state with its degree);
2. the attentional layer (34) with attention `a`: its output is `Φ (h u) X_{N_u}`;
3. the message-passing layer (35) with message `ψ`: its output is `Φ (h u) X_{N_u}`.

**Formalization Note.** In clause 1 `Φ` also receives each neighbour's degree `|N_v|`: with the
Kipf–Welling coefficient `1/√(d_u d_v)` the output of (33) depends on neighbour degrees, which
`X_{N_u}` does not record (a featureless node of degree 2 whose neighbours have degree 1, resp. 2,
gets `√2`, resp. `1`, with `ψ ≡ 1`, `⊕ = Σ`). `|N_u|` is the size of the multiset. Hence every stack
of flavour layers is a `LocalGNN`. -/
theorem flavours_are_local {H M A H' : Type*} [AddCommMonoid M] [Module ℝ M] {M' : Type*}
    (κ : H → H → ℕ → ℕ → ℝ) (a : H → H → ℝ) (ψ : H → M) (ψmp : H → H → M')
    (agg : Multiset M → A) (aggmp : Multiset M' → A) (φ : H → A → H') :
    (∃ Φ : H → Multiset (H × ℕ) → H', ∀ (V : Type w) [Fintype V] (E : V → V → Prop)
        [DecidableRel E] (h : V → H) (u : V),
        convLayer κ ψ agg φ E h u =
          Φ (h u) ((nbhd E u).val.map (fun v => (h v, (nbhd E v).card)))) ∧
    (∃ Φ : H → Multiset H → H', ∀ (V : Type w) [Fintype V] (E : V → V → Prop)
        [DecidableRel E] (h : V → H) (u : V),
        attnLayer a ψ agg φ E h u = Φ (h u) ((nbhd E u).val.map h)) ∧
    (∃ Φ : H → Multiset H → H', ∀ (V : Type w) [Fintype V] (E : V → V → Prop)
        [DecidableRel E] (h : V → H) (u : V),
        mpLayer ψmp aggmp φ E h u = Φ (h u) ((nbhd E u).val.map h)) := by sorry

end GeometricDL.WL
