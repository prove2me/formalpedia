-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_19
-- name    : GraphonCheeger.Supplement.theorem_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:36:13.685099+00:00
-- url     : https://prove2.me/theorems/5d185452-b925-4eef-8931-46c013b6478e
-- title:
--   Theorem 5.19 — $q^*(G)=\hat q^*_{\mathrm{pure}}(W'_G)$ and $q^*_{\mathrm{frac}}(G)=\hat q^*_{\mathrm{mix}}(W'_G)=\hat q^*_{\mathrm{mix}}(W_G)=\hat q^*_{\mathrm{pure}}(W_G)$, also for each $\kappa$
-- statement:
--   Let $G$ be a graph on $n\ge1$ vertices and let $W'_G$ and $W_G$ be the atomic and continuous graphons of Example 2.4. Then
--   $$
--   q^*(G)=\hat q^*_{\mathrm{pure}}(W'_G),\qquad
--   q^*_{\mathrm{frac}}(G)=\hat q^*_{\mathrm{mix}}(W'_G)=\hat q^*_{\mathrm{mix}}(W_G)=\hat q^*_{\mathrm{pure}}(W_G).
--   $$
--   The same equalities hold for $\kappa$-modularity for every fixed $\kappa\ge1$:
--   $$
--   q^*_\kappa(G)=\hat q^*_{\kappa,\mathrm{pure}}(W'_G),\qquad
--   q^*_{\kappa,\mathrm{frac}}(G)=\hat q^*_{\kappa,\mathrm{mix}}(W'_G)=\hat q^*_{\kappa,\mathrm{mix}}(W_G)=\hat q^*_{\kappa,\mathrm{pure}}(W_G).
--   $$
--
--   Graph modularity is pure modularity of the atomic graphon, while fractional modularity is the (invariant) mixed modularity of either graphon of $G$; the two may differ (Example 5.20, $C_5$).
--
--   **Formalization Note** $G$ is a graph on `Fin n`; $W'_G$ and $W_G$ are the base `atomicGraphon` (with `atomicMeasure n`) and `stepGraphon`. $q^*_\kappa(G)$ and $q^*_{\kappa,\mathrm{frac}}(G)$ are not displayed in the paper; they are taken as fixed by its proof: the maximum over partitions into at most $\kappa$ parts, and the supremum over fractional $\kappa$-partitions.
--
--   Differences from the source:
--   - encoding: a graph G → a graph on Fin n with n ≥ 1; reason: every finite graph is isomorphic to one on Fin n; n ≥ 1 excludes only the empty vertex set, where W′_G has no probability measure
--   - reading: κ-modularity q*_κ(G) and fractional κ-modularity q*_{κ,frac}(G) (used, not defined) → modularityK κ: max over χ : V → [κ] of q(G, A_χ); modularityFracK κ: sup over fractional κ-partitions; reason: the proof of Theorem 5.19 and Lemma 5.21 (p.65) use exactly these
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.19, p.63 (PDF p.63)

import Mathlib
import Definitions.Def_GraphonCheeger_stepGraphon
import Definitions.Def_GraphonCheeger_Supplement_graphModularity
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 5.19, p.63 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `G` be a graph and let `W′_G` and `W_G` be the corresponding graphons of
Example 2.4. Then `q*(G) = q̂*_pure(W′_G)` (5.77) and
`q*_frac(G) = q̂*_mix(W′_G) = q̂*_mix(W_G) = q̂*_pure(W_G)` (5.78). The same equalities hold also for
`κ`-modularity, for every fixed `κ ≥ 1`.

**Formalization Note.** `G` is a graph on `Fin n` with `n ≥ 1` (so that `W′_G` lives on a
probability space); `W′_G` is the base `atomicGraphon` with `atomicMeasure n`, `W_G` the base
`stepGraphon` on `[0, 1]`. For `κ`-modularity, `q*_κ(G)` (`modularityK`) and `q*_{κ,frac}(G)`
(`modularityFracK`) are as fixed by the proof of the theorem (p.63): the maximum over partitions
into at most `κ` parts, and the supremum over fractional `κ`-partitions. -/
theorem theorem_5_19 {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    modularity G = modPure (atomicMeasure n) (atomicGraphon G) ∧
    modularityFrac G = modW (atomicMeasure n) (atomicGraphon G) ∧
    modW (atomicMeasure n) (atomicGraphon G) = modW volume (stepGraphon G) ∧
    modW volume (stepGraphon G) = modPure volume (stepGraphon G) ∧
    ∀ κ : ℕ, 1 ≤ κ →
      modularityK κ G = modPureK κ (atomicMeasure n) (atomicGraphon G) ∧
      modularityFracK κ G = modK κ (atomicMeasure n) (atomicGraphon G) ∧
      modK κ (atomicMeasure n) (atomicGraphon G) = modK κ volume (stepGraphon G) ∧
      modK κ volume (stepGraphon G) = modPureK κ volume (stepGraphon G) := by sorry

end GraphonCheeger.Supplement
