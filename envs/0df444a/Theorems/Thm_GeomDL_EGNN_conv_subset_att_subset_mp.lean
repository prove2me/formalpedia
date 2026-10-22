-- Prove2me | Theorems.Thm_GeomDL_EGNN_conv_subset_att_subset_mp
-- name    : GeomDL.EGNN.conv_subset_att_subset_mp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:15.904838+00:00
-- url     : https://prove2.me/theorems/c1afa3ce-07aa-4ead-bce8-433e31d0c406
-- title:
--   §5.3, pp. 79–80 — representational containment: convolution ⊆ attention ⊆ message passing
-- statement:
--   Fix a graph with adjacency matrix $\mathbf A$ and neighbourhoods $\mathcal N_u$, node features $\mathbf x_u$, an update $\phi$, a feature map $\psi$ and an aggregator $\bigoplus$. Then:
--   1. for every attention mechanism $a$, the attentional layer (34) equals the message-passing layer (35) with messages $\psi'(\mathbf x_u,\mathbf x_v) = a(\mathbf x_u,\mathbf x_v)\psi(\mathbf x_v)$;
--   2. if the features identify the nodes ($u\mapsto\mathbf x_u$ injective), then for every coefficient matrix $(c_{uv})$ there is an attention mechanism $a$ (a look-up table with $a(\mathbf x_u,\mathbf x_v) = c_{uv}$) for which the convolutional layer (33) equals the attentional layer (34);
--   3. under the same hypothesis, for every $(c_{uv})$ there is a message function $\psi'$ (with $\psi'(\mathbf x_u,\mathbf x_v) = c_{uv}\psi(\mathbf x_v)$) for which (33) equals (35).
--
--   In symbols, writing $\mathrm{Conv}_c$, $\mathrm{Att}_a$, $\mathrm{MP}_{\psi'}$ for the three layers on the same input,
--   $$\mathrm{Att}_a = \mathrm{MP}_{a\psi}, \qquad \mathbf x \text{ injective} \implies \exists a,\ \mathrm{Conv}_c = \mathrm{Att}_a \ \text{ and } \ \exists \psi',\ \mathrm{Conv}_c = \mathrm{MP}_{\psi'}.$$
--
--   This is the book's "convolution ⊆ attention ⊆ message-passing": the message-passing flavour is the most expressive of the three.
--
--   **Formalization Note** The injectivity hypothesis in parts 2 and 3 is added and is necessary: an attention mechanism or message function sees only features, so if two nodes $u \neq u'$ have equal features but $c_{uv}\neq c_{u'v'}$ for $\mathbf x_v=\mathbf x_{v'}$, no look-up table $a(\mathbf x_u,\mathbf x_v)=c_{uv}$ exists (a two-node counterexample is checked in Lean). Part 1 needs no hypothesis. The coefficients act on the messages through a scalar multiplication `SMul ℝ M`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.3, pp. 79–80, "convolution ⊆ attention ⊆ message-passing", eqs. (33)–(35)

import Mathlib
import Definitions.Def_GeomDL_EGNN_Defs

namespace GeomDL.EGNN

/-- §5.3, pp. 79–80: the containment "convolution ⊆ attention ⊆ message-passing".
(1) Every attentional layer (34) is the message-passing layer (35) with messages
`ψ(x_u, x_v) = a(x_u, x_v) ψ(x_v)`. (2) On features that identify the nodes (`u ↦ x_u`
injective), the convolutional layer (33) with coefficients `c_{uv}` equals an attentional layer
whose attention is a look-up table `a(x_u, x_v) = c_{uv}`, and (3) equals a message-passing
layer with messages `ψ'(x_u, x_v) = c_{uv} ψ(x_v)`. -/
theorem conv_subset_att_subset_mp {n : ℕ} {α M M' β : Type*} [SMul ℝ M]
    (φ : α → M' → β) (agg : Multiset M → M') (ψ : α → M) (X : Fin n → α)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ a : α → α → ℝ,
        attLayer φ agg a ψ X A = mpLayer φ agg (fun xu xv => a xu xv • ψ xv) X A) ∧
    (Function.Injective X → ∀ c : Matrix (Fin n) (Fin n) ℝ,
        ∃ a : α → α → ℝ, convLayer φ agg c ψ X A = attLayer φ agg a ψ X A) ∧
    (Function.Injective X → ∀ c : Matrix (Fin n) (Fin n) ℝ,
        ∃ ψ' : α → α → M, convLayer φ agg c ψ X A = mpLayer φ agg ψ' X A) := by sorry

end GeomDL.EGNN
