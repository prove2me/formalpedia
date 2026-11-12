-- Prove2me | Theorems.Thm_MinorFreeOracle_LinearSpace_lemma_40
-- name    : MinorFreeOracle.LinearSpace.lemma_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:15.24529+00:00
-- url     : https://prove2.me/theorems/ff0aee7f-0ffa-458c-b922-2d13c6d45dd9
-- title:
--   Lemma 40 — distances under cyclic copy expansion (generalized)
-- statement:
--   Let G be a connected finite undirected graph with nonnegative real edge weights. Form its cyclic copy expansion as specified in the definition, including the chosen edge lifts and optional subdivisions, and let ρ be its prescribed projection. Then ρ is surjective, and for every pair of original vertices s,t and every choice of copies s̄,t̄ above them,
--
--   $$
--   d_G(s,t)=d_{\bar G}(\bar s,\bar t).
--   $$
--
--   This includes the scaffolding operation with relabeled vortices of Section 7.1. The graph and its projection are constructed from the copy data; an arbitrary graph satisfying a distance identity is not being postulated. The theorem retains all choices of endpoint copies, including subdivision vertices.
--
--   Differences from the source:
--   - generalization: the specific scaffolding of an apex-free almost-embeddable graph with relabeled vortices → every connected nonnegatively weighted edge-list graph, with arbitrary positive cyclic copy counts, positive edge-lift counts and optional edge subdivisions; reason: the source construction is obtained by taking facial corners in local rotation order as copies, two lifts per embedded edge and one per vortex edge, subdividing the embedded edges; untouched vertices have one copy
--   - encoding: a natural projection onto the original vertices and arbitrary choices of copies → the explicitly constructed projection on finite enumerations, with surjectivity included in the conclusion; reason: enumerating the output changes no vertex or edge, and surjectivity makes existence of endpoint copies explicit
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, Lemma 40, PDF p.36 (printed p.34); construction §3.2, PDF p.17 and §7.1, PDF pp.35–36

import Mathlib
import Definitions.Def_MinorFreeOracle_LinearSpace_CopyExpansion

namespace MinorFreeOracle.LinearSpace

/-- Oh, Lemma 40, PDF p.36 (printed p.34). Generalized to any nonempty cyclic vertex-copy
expansion with a positive number of lifts of each old edge, followed by optional subdivisions.
The scaffolding of §3.2 and §7.1 is this construction with copies indexed by facial corners.
Both the graph and its natural projection are computed from the construction data. -/
theorem lemma_40 (G : TZLevelsADO.Graph) (hconn : G.Connected)
    (hnonneg : ∀ e, 0 ≤ G.wt e) (D : CopyExpansion G) (K : D.Subdivision) :
    Function.Surjective (D.projection K) ∧
    ∀ (s t : Fin G.n) (sbar tbar : Fin (D.graph K).n),
      D.projection K sbar = s → D.projection K tbar = t →
      TZLevelsADO.dist G s t = TZLevelsADO.dist (D.graph K) sbar tbar := by sorry

end MinorFreeOracle.LinearSpace
