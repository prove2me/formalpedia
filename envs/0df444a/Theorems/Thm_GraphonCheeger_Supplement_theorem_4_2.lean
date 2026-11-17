-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_2
-- name    : GraphonCheeger.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:28:12.269081+00:00
-- url     : https://prove2.me/theorems/ebc23be1-0581-4d7a-8d90-c0417fc9d72a
-- title:
--   Theorem 4.2 — $\mathrm{MC}(G)=\mathrm{MC}_{\mathrm{frac}}(G)=\mathrm{MC}_{\mathrm{pure}}(W'_G)=\mathrm{MC}_{\mathrm{mix}}(W'_G)=\mathrm{MC}_{\mathrm{pure}}(W_G)=\mathrm{MC}_{\mathrm{mix}}(W_G)$
-- statement:
--   Let $G$ be a graph on $n\ge1$ vertices, and let $W'_G$ (the adjacency matrix on $V(G)$ with the uniform probability measure) and $W_G$ (its step graphon on $[0,1]$) be the atomic and continuous graphons of Example 2.4. Then
--   $$
--   \mathrm{MC}(G)=\mathrm{MC}_{\mathrm{frac}}(G)=\mathrm{MC}_{\mathrm{pure}}(W'_G)=\mathrm{MC}_{\mathrm{mix}}(W'_G)=\mathrm{MC}_{\mathrm{pure}}(W_G)=\mathrm{MC}_{\mathrm{mix}}(W_G).
--   $$
--
--   The graph maximum cut, its fractional relaxation, and the pure and mixed graphon maximum cuts of both graphons of $G$ all coincide; this is the base case for the convergence results of §4.1.
--
--   **Formalization Note** $G$ is a graph on `Fin n`; $W'_G$ and $W_G$ are the base `atomicGraphon` (with `atomicMeasure n`) and `stepGraphon`. The six-term chain is five consecutive equalities.
--
--   Differences from the source:
--   - encoding: a graph G → a graph on Fin n with n ≥ 1; reason: every finite graph is isomorphic to one on Fin n; n ≥ 1 excludes only the empty vertex set, where n^{-2} and W_G, W′_G are undefined
--   - encoding: mixed 2-colouring Ψ = (ψ, 1 − ψ) → ψ : Ω → [0, 1] measurable (base IsColouring); C(W, Ψ) is the base cutVal; reason: the identification the paper makes (pp.31–32)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.2, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_maxCut
import Definitions.Def_GraphonCheeger_stepGraphon

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 4.2, p.32 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `G` be a graph and let `W′_G` and `W_G` be the corresponding atomic and
continuous graphons of Example 2.4. Then
`MC(G) = MC_frac(G) = MC_pure(W′_G) = MC_mix(W′_G) = MC_pure(W_G) = MC_mix(W_G)` (4.20).

**Formalization Note.** `G` is a graph on `Fin n` with `n ≥ 1` (the normalisation `n^{-2}` and the
construction of `W_G`, `W′_G` need a vertex); `W′_G` is the base `atomicGraphon` on `Fin n` with the
uniform measure `atomicMeasure n`, and `W_G` the base `stepGraphon` on `[0, 1]`. The six-term chain
is stated as five consecutive equalities. -/
theorem theorem_4_2 {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    maxCutG G = maxCutFrac G ∧
    maxCutFrac G = maxCutPure (atomicMeasure n) (atomicGraphon G) ∧
    maxCutPure (atomicMeasure n) (atomicGraphon G) = maxCutMix (atomicMeasure n) (atomicGraphon G) ∧
    maxCutMix (atomicMeasure n) (atomicGraphon G) = maxCutPure volume (stepGraphon G) ∧
    maxCutPure volume (stepGraphon G) = maxCutMix volume (stepGraphon G) := by sorry

end GraphonCheeger.Supplement
