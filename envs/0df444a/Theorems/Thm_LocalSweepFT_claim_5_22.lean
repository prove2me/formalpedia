-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_22
-- name    : LocalSweepFT.claim_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:40:08.849207+00:00
-- url     : https://prove2.me/theorems/988be06b-ea62-488c-8856-b582801779ee
-- title:
--   Claim 5.22 — slices with the same time are equal or have disjoint histories
-- statement:
--   Let $(G,T)$ be a space–time graph and $K_1,K_2$ slices with $T(K_1)=T(K_2)$. Then either $K_1=K_2$ or the histories $H_{K_1}$ and $H_{K_2}$ are disjoint.
--
--   Slices of the same time are induced by disjoint sets of faults, which is what makes the fault counts of different slices add up.
--
--   Differences from the source:
--   - encoding: slices K₁, K₂ with T(K₁) = T(K₂) → the slices of two vertices u₁, u₂ with T(u₁) = T(u₂); reason: every slice is the slice of each of its vertices, with that vertex's history
--   - reading: history: vertices of time ≤ T(u) connected to u by a path of arrows (Def 5.21) → paths inside the vertices of time ≤ T(u); reason: the reading under which the proof goes through
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.22, p.48

import Mathlib
import Definitions.Def_LocalSweepFT_SpaceTimeGraph

namespace LocalSweepFT

/-- Claim 5.22, p.48 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `K₁, K₂` be two slices of a space–time graph with
`T(K₁) = T(K₂)`. Then either `K₁ = K₂` or `H_{K₁}` and `H_{K₂}` are disjoint.

**Formalization Note.** Every slice is the slice of each of its vertices, with history the history
of that vertex; the claim is stated for the slices `slice u₁`, `slice u₂`. -/
theorem claim_5_22 {V : Type} (G : SpaceTimeGraph V) (u₁ u₂ : V) (ht : G.T u₁ = G.T u₂) :
    G.slice u₁ = G.slice u₂ ∨ Disjoint (G.hist u₁) (G.hist u₂) := by sorry

end LocalSweepFT
