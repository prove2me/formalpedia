-- Prove2me | Theorems.Thm_GraphonCheeger_theorem_4_20
-- name    : GraphonCheeger.theorem_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:27.825409+00:00
-- url     : https://prove2.me/theorems/ef4b5847-707e-462c-9299-438c62d91f03
-- title:
--   Theorem 4.20: $h(G)=h_{\mathrm{pure}}(W'_G)$ and $\tilde h(G)=h_{\mathrm{mix}}(W'_G)=h_{\mathrm{pure}}(W_G)=h_{\mathrm{mix}}(W_G)\le h(G)$
-- statement:
--   Let $G$ be a graph, and let $W'_G$ and $W_G$ be its atomic and continuous graphons. Then
--
--   $$h(G)=h_{\mathrm{pure}}(W'_G),$$
--
--   $$\tilde h(G)=h_{\mathrm{mix}}(W'_G)=h_{\mathrm{pure}}(W_G)=h_{\mathrm{mix}}(W_G).$$
--
--   Furthermore $\tilde h(G)\le h(G)$, and the inequality may be strict: there is a graph with no isolated vertices and $\tilde h(G)<h(G)$ (for $K_3$, $h=1$ and $\tilde h=1/2$).
--
--   The theorem identifies the fractional Cheeger constant of a graph with the Cheeger constant of its step graphon, which is how graph Cheeger constants enter the graphon theory.
--
--   Differences from the source:
--   - encoding: "let $G$ be a graph" → (4.87) is stated for graphs with at least one edge, and (4.86) and $\tilde h(G)\le h(G)$ for graphs with $n\ge1$ vertices and no isolated vertices; reason: these are the conditions under which the quantities are defined ((4.83) defines $h(W)$ only for $\rho_W>0$; Definition 4.19 defines $h(G)$ only without isolated vertices); they exclude only undefined cases.
--   - encoding: "we may have strict inequality" → the existence of a graph on `Fin m`, $m\ge1$, with no isolated vertices and $\tilde h<h$; reason: the paper's assertion is existential (its example is $K_3$, p.43).
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Theorem 4.20, (4.86)–(4.87), p.43

import Mathlib
import Definitions.Def_GraphonCheeger_stepGraphon
import Definitions.Def_GraphonCheeger_cheegerG
import Definitions.Def_GraphonCheeger_fracCheeger
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory

namespace GraphonCheeger

/-- Theorem 4.20, p.43 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for a graph `G` with atomic graphon `W′_G` and continuous graphon
`W_G` (Example 2.4), `h(G) = h_pure(W′_G)` (4.86), `h̃(G) = h_mix(W′_G) = h_pure(W_G) = h_mix(W_G)`
(4.87), and `h̃(G) ≤ h(G)`, where the inequality may be strict.

**Formalization Note.** Each clause carries the standing assumption under which its quantities
are defined: (4.87) needs `ρ > 0`, i.e. `G` has an edge ((4.83) defines `h(W)` only when
`ρ_W > 0`); (4.86) and `h̃(G) ≤ h(G)` involve `h(G)`, which Definition 4.19 defines for graphs
with at least one vertex and no isolated vertices. "We may have strict inequality" is the
existence of a graph with no isolated vertices and `h̃ < h` (the paper's example is `K₃`). -/
theorem theorem_4_20 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((∃ u v : Fin n, G.Adj u v) →
      fracCheeger G = cheegerW (atomicMeasure n) (atomicGraphon G) ∧
      cheegerW (atomicMeasure n) (atomicGraphon G) = cheegerPure volume (stepGraphon G) ∧
      cheegerPure volume (stepGraphon G) = cheegerW volume (stepGraphon G)) ∧
    (0 < n → (∀ v : Fin n, 0 < G.degree v) →
      cheegerG G = cheegerPure (atomicMeasure n) (atomicGraphon G) ∧
      fracCheeger G ≤ cheegerG G) ∧
    (∃ (m : ℕ) (H : SimpleGraph (Fin m)) (_ : DecidableRel H.Adj),
      0 < m ∧ (∀ v : Fin m, 0 < H.degree v) ∧ fracCheeger H < cheegerG H) := by sorry

end GraphonCheeger
