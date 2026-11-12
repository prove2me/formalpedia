-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_24
-- name    : LocalSweepFT.claim_5_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:59.954387+00:00
-- url     : https://prove2.me/theorems/43b0cab1-99e5-4500-933c-a0eaab472956
-- title:
--   Claim 5.24 — the graph $G_K$ of a slice is connected
-- statement:
--   Let $(G,T)$ be a space–time graph and $K$ the slice of a vertex $u$. Any two vertices of the graph $G_K$ (the slices $R\subseteq H_K$ with $T(R)=T(K)-1$, adjacent when a fork joins them) are joined by a path; and if $K\ne H_K$, then $G_K$ is nonempty, hence connected.
--
--   It lets a spanning tree of a slice's history be assembled from spanning trees of its predecessor slices (Claim 5.26).
--
--   Differences from the source:
--   - reading: "G_K is connected" → G_K is preconnected for every slice, and connected (nonempty) when K ≠ H_K; reason: when K = H_K the graph has no vertices; the claim is used for K ≠ H_K (Claim 5.26)
--   - reading: history: vertices of time ≤ T(u) connected to u by a path of arrows (Def 5.21) → paths inside the vertices of time ≤ T(u); reason: the reading under which the proof goes through
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.24, p.48

import Mathlib
import Definitions.Def_LocalSweepFT_SpaceTimeGraph

namespace LocalSweepFT

/-- Claim 5.24, p.48 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). The graph `G_K` of a slice `K` (Def 5.23) is
connected.

**Formalization Note.** Stated for the slice `K` of any vertex `u`: any two vertices of `G_K` are
joined by a path (`Preconnected`), and `G_K` is nonempty, hence `Connected` in Mathlib's sense,
whenever `K ≠ H_K` (when `K = H_K`, `G_K` has no vertices). -/
theorem claim_5_24 {V : Type} (G : SpaceTimeGraph V) (u : V) :
    (G.sliceGraph u).Preconnected ∧ (G.slice u ≠ G.hist u → (G.sliceGraph u).Connected) := by sorry

end LocalSweepFT
