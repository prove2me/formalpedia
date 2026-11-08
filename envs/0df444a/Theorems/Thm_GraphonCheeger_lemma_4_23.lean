-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_23
-- name    : GraphonCheeger.lemma_4_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:03:55.571472+00:00
-- url     : https://prove2.me/theorems/e0cd6262-69d4-4895-94fd-0c2d5b1c7d35
-- title:
--   Lemma 4.23: $\tilde h(G)\ge h(G)\bigl(1-\sqrt{\sum d_v^2}/\sum d_v\bigr)$ and $0\le h(G)-h(W_G)\le\sqrt{d_{\max}/\mathrm{vol}(G)}$
-- statement:
--   Let $G$ be a finite simple graph with $n\ge1$ vertices and no isolated vertices, with degrees $d_v$, maximum degree $d_{\max}$ and $\mathrm{vol}(G)=\sum_vd_v$. Then $h(W_G)=\tilde h(G)$,
--
--   $$\tilde h(G)\ \ge\ h(G)\Bigl(1-\frac{\sqrt{\sum_vd_v^2}}{\sum_vd_v}\Bigr),$$
--
--   which for $h(G)>0$ is the printed bound $\dfrac{h(W_G)}{h(G)}=\dfrac{\tilde h(G)}{h(G)}\ge1-\dfrac{\sqrt{\sum_vd_v^2}}{\sum_vd_v}$, and
--
--   $$0\ \le\ h(G)-h(W_G)\ \le\ \frac{\sqrt{\sum_vd_v^2}}{\mathrm{vol}(G)}\ \le\ \sqrt{\frac{d_{\max}}{\mathrm{vol}(G)}} .$$
--
--   For dense graphs the right-hand side is of order $n^{-1/2}$, so the Cheeger constant of a graph and of its step graphon become indistinguishable as the graph grows.
--
--   Differences from the source:
--   - generalization: $\dfrac{h(W_G)}{h(G)}=\dfrac{\tilde h(G)}{h(G)}\ge1-\dfrac{\sqrt{\sum d_v^2}}{\sum d_v}$ → $h(W_G)=\tilde h(G)$ and $\tilde h(G)\ge h(G)\bigl(1-\sqrt{\sum d_v^2}/\sum d_v\bigr)$; reason: when $h(G)>0$ the two are equivalent; when $h(G)=0$ (a disconnected graph, e.g. two disjoint triangles) the printed ratio is $0/0$, and the multiplied form remains meaningful.
--   - encoding: finite simple graph → a graph on `Fin n` with $n\ge1$; reason: $h(G)$ is defined only for graphs with vertices (Definition 4.19), and every finite graph is isomorphic to one on `Fin n`.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.23, (4.90)–(4.91), p.44

import Mathlib
import Definitions.Def_GraphonCheeger_stepGraphon
import Definitions.Def_GraphonCheeger_cheegerG
import Definitions.Def_GraphonCheeger_fracCheeger
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory SpectralSparsify.Decomp

namespace GraphonCheeger

/-- Lemma 4.23, p.44 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for a finite simple graph `G` with no isolated vertices,
`h(W_G)/h(G) = h̃(G)/h(G) ≥ 1 − √(Σ_v d_v²)/Σ_v d_v` (4.90) and
`0 ≤ h(G) − h(W_G) ≤ √(Σ_v d_v²)/vol(G) ≤ √(d_max/vol(G))` (4.91).

**Formalization Note.** (4.90) is stated as `h(W_G) = h̃(G)` together with the multiplied form
`h̃(G) ≥ h(G)·(1 − √(Σ d_v²)/Σ d_v)`: when `h(G) > 0` this is (4.90); when `h(G) = 0` (a
disconnected graph) the printed ratio is `0/0`. `0 < n` is part of Definition 4.19's setting;
`d_max = max_v d_v` is Mathlib's `G.maxDegree`. -/
theorem lemma_4_23 {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hiso : ∀ v : Fin n, 0 < G.degree v) :
    cheegerW volume (stepGraphon G) = fracCheeger G ∧
    cheegerG G * (1 - Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2) / ∑ v, (G.degree v : ℝ))
      ≤ fracCheeger G ∧
    0 ≤ cheegerG G - cheegerW volume (stepGraphon G) ∧
    cheegerG G - cheegerW volume (stepGraphon G)
      ≤ Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2) / vol G Finset.univ ∧
    Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2) / vol G Finset.univ
      ≤ Real.sqrt ((G.maxDegree : ℝ) / vol G Finset.univ) := by sorry

end GraphonCheeger
