-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_2_11
-- name    : GraphonCheeger.Supplement.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:23:38.43603+00:00
-- url     : https://prove2.me/theorems/1952d0b4-5f79-458e-8eac-bc7013345ab1
-- title:
--   Theorem 2.11 — graphon representation of $\kappa$-coloured graph limits
-- statement:
--   Let $\kappa\ge1$ and let $W=(W,\Psi)$ be a $\kappa$-coloured graphon on a probability space $(\Omega,\mathcal F,\mu)$. Then $W$ defines a coloured graph limit
--   $$
--   \widehat W=\tau(W)=\bigl(t(F,W)\bigr)_F\in\widehat{\mathcal W}_\kappa ,
--   $$
--   and the following hold.
--
--   1. Every coloured graph limit is $\tau(W_0)$ for some coloured graphon $W_0$, which may be chosen as a pure coloured graphon $(W_0,\chi)$ on $[0,1]$.
--   2. Two coloured graphons define the same graph limit if and only if they are equivalent.
--   3. If $(G_n)$ are $\kappa$-coloured graphs with $|G_n|\to\infty$, then $G_n\to W$ if and only if $t(F,G_n)\to t(F,W)$ for every coloured graph $F$.
--   4. The random coloured graphs $G(n,W)$ converge to $W$ almost surely.
--
--   The theorem is the coloured version of the graphon representation of graph limits: it lets every statement about coloured graph limits be phrased with graphons, and it is used throughout §§2–5.
--
--   **Formalization Note** Graph limits are points of $\mathbb R^L$ (Definition 3.5 (W1)); $G_n\to\widehat W$ means $\tau(G_n)\to\widehat W$ in the product topology. In clause 4 the graphs $G(n,W)$ are the induced subgraphs on $[n]$ of one random $G(\infty,W)$, realised on the product space `sampleMeasure μ`. With equivalence defined by equal densities, clause 2 follows directly from the definitions, as in the paper.
--
--   Differences from the source:
--   - encoding: test graphs F ∈ U (unlabelled coloured graphs); limits as points of [0,1]^U → labelled coloured graphs on Fin (n+1) (LIdx κ); points of ℝ^L with the product topology; reason: t(F, ·) is invariant under relabelling (p.8), so equalities, convergence and limits over L and U agree; ℝ^L only changes the ambient space
--   - encoding: W₁ ≅ W₂ (Definition 2.6: one, and thus all, of the conditions of Lemma 2.5) → CEquiv: t(F, W₁) = t(F, W₂) for every coloured graph F; reason: condition (i) of Lemma 2.5, which Definition 2.6 lists as equivalent to the others
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
--   - encoding: κ ≥ 1 (Definition 2.1) → [NeZero κ]; reason: the same condition
--   - encoding: G(n, W) for n ∈ ℕ, induced subgraphs of G(∞, W) on one probability space → sampleGraph W Ψ n ω on the product space sampleMeasure μ (X_i ∼ μ, uniform U_{ij}, V_i, all independent); reason: this construction has the joint law of §2.1.1, so the almost sure statement is the same
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 2.11, p.10 (PDF p.10)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_sampleGraph

open MeasureTheory Filter Topology

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 2.11, p.10 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): each coloured graphon `W` defines a coloured graph limit `Ŵ = τ(W)`
such that (i) every graph limit is given by some coloured graphon, which may be chosen pure on
`Ω = [0, 1]`; (ii) two coloured graphons define the same graph limit iff they are equivalent;
(iii) for coloured graphs `G_n` with `|G_n| → ∞`, `G_n → W` iff `t(F, G_n) → t(F, W)` for every
`F` (2.5); (iv) the random coloured graphs `G(n, W) → W` almost surely.

**Formalization Note.**
* Graph limits are Definition 3.5 (W1): `Ŵ_κ = GraphLimitSpace κ ⊂ ℝ^L`, with `L` the labelled
  coloured graphs (`LIdx κ`), and the limit defined by `W` is `τ(W) = (t(F, W))_F`; `G_n → Ŵ`
  means `τ(G_n) → Ŵ` in the product topology (Def. 3.5 (W1)).
* `W` lives on an arbitrary probability space `(Ω, µ)`; in (ii) the second graphon lives on a
  possibly different space. A pure colouring `χ` is the point-mass colouring `ofColour χ`.
* In (iv), `G(n, W)` for all `n` are the induced subgraphs on `[n]` of one random `G(∞, W)`,
  realized on `sampleMeasure µ` (`sampleGraph`, §2.1.1). `κ ≥ 1` is `[NeZero κ]`. -/
theorem theorem_2_11 (κ : ℕ) [NeZero κ] {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ) (hW : IsGraphon W)
    (hΨ : IsKColouring Ψ) :
    tau μ W Ψ ∈ GraphLimitSpace κ ∧
    (∀ w ∈ GraphLimitSpace κ, ∃ (W₀ : unitInterval → unitInterval → ℝ) (χ : unitInterval → Fin κ),
      IsGraphon W₀ ∧ Measurable χ ∧ tau volume W₀ (ofColour χ) = w) ∧
    (∀ (Ω₂ : Type v) [MeasurableSpace Ω₂] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
        (W₂ : Ω₂ → Ω₂ → ℝ) (Ψ₂ : Ω₂ → Fin κ → ℝ), IsGraphon W₂ → IsKColouring Ψ₂ →
        (tau μ W Ψ = tau μ₂ W₂ Ψ₂ ↔ CEquiv μ W Ψ μ₂ W₂ Ψ₂)) ∧
    (∀ (N : ℕ → ℕ) (G : (n : ℕ) → CGraph κ (N n)), Tendsto N atTop atTop →
      (Tendsto (fun n => tauG (G n)) atTop (𝓝 (tau μ W Ψ)) ↔
        ∀ F : LIdx κ, Tendsto (fun n => homDensG F.2 (G n)) atTop (𝓝 (homDens μ W Ψ F.2)))) ∧
    (∀ᵐ ω ∂(sampleMeasure μ),
      Tendsto (fun n => tauG (sampleGraph W Ψ n ω)) atTop (𝓝 (tau μ W Ψ))) := by sorry

end GraphonCheeger.Supplement
