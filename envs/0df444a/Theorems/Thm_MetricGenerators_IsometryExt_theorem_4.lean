-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_theorem_4
-- name    : MetricGenerators.IsometryExt.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:53.890889+00:00
-- url     : https://prove2.me/theorems/548ea90d-37cc-4bfe-8bb4-ffdeac426f92
-- title:
--   Theorem 4, p. 388 — with H − T a forest, f extends to an isometry of H iff H has a representation in G; then C* is the greatest representation
-- statement:
--   Let $H$ and $G$ be finite connected graphs, let $T$ be a strong metric generator of $H$ such that $H-T$ (the subgraph of $H$ induced on $V(H)\setminus T$) is a forest, and let $f:(T,\mu_H|_T)\to G$ be an isometry. Then:
--
--   1. there exists an isometry $\bar f:V(H)\to V(G)$ from $H$ to $G$ extending $f$ if and only if there exist sets $C_u$ ($u\in V(H)$) that represent $H$ in $G$ with respect to $T$;
--   2. if such an isometry exists, the sets $C^*_u$ ($u\in V(H)$) produced by the candidate procedure are the unique inclusionwise maximal sets that represent $H$ in $G$ with respect to $T$: they form a representation, and
--   $$C_u\subseteq C^*_u\quad(u\in V(H))\qquad\text{for every representation } (C_u)_{u\in V(H)}.$$
--
--   The theorem gives a good characterization of the extendability of an isometry given on a strong metric generator, under the forest condition; Figure 2 of the paper shows the characterization fails when $H-T$ contains a triangle.
--
--   **Formalization Note** "Unique inclusionwise maximal" is encoded as "$C^*$ is a representation containing every representation", i.e. a greatest element for componentwise inclusion, which is in particular the unique maximal one. An isometry here preserves all distances, not just adjacency.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 388, Theorem 4

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, p. 388, **Theorem 4** (both paragraphs). Let `H` and `G` be finite connected graphs,
`T` a strong metric generator of `H` such that `H − T` (the subgraph of `H` induced on
`V(H) ∖ T`) is a forest, and `f : (T, μ_H|T) → G` an isometry. Then
1. there is an isometry from `H` to `G` extending `f` if and only if there exist sets `C_u`
   (`u ∈ V(H)`) that represent `H` in `G` with respect to `T`;
2. if such an isometry exists, the sets `C*_u` represent `H` in `G` with respect to `T` and
   contain every representation (`C_u ⊆ C*_u` for all `u`).

Formalization Note: "the sets `C*_u` are the unique inclusionwise maximal sets that represent
`H`" is encoded as "`C*` is a representation that contains every representation" (a greatest
element of the representations under componentwise inclusion). A greatest element is the unique
maximal element; this is also what the paper's proof establishes. -/
theorem theorem_4 {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsStrongMetricGenerator H T)
    (hforest : (H.induce ((↑T : Set VH)ᶜ)).IsAcyclic)
    (f : ↥T → VG) (hf : IsIsometryOn H G T f) :
    ((∃ φ : VH → VG, IsIsometry H G φ ∧ Extends T f φ) ↔
      (∃ C : VH → Set VG, Represents H G T f C)) ∧
    ((∃ φ : VH → VG, IsIsometry H G φ ∧ Extends T f φ) →
      Represents H G T f (cStar H G T f) ∧
      ∀ C : VH → Set VG, Represents H G T f C → ∀ u : VH, C u ⊆ cStar H G T f u) := by sorry

end MetricGenerators.IsometryExt
