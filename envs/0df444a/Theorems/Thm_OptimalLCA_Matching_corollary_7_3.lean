-- Prove2me | Theorems.Thm_OptimalLCA_Matching_corollary_7_3
-- name    : OptimalLCA.Matching.corollary_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:48:04.634956+00:00
-- url     : https://prove2.me/theorems/587a29de-ffd8-4bc3-b178-787bc2d781d3
-- title:
--   Corollary 7.3 (for any proposal law with the guarantee of Lemma 7.1) — (1 − ε/16)ν_f(G) ≤ ES/(2K) ≤ ν_f(G)
-- statement:
--   Let $G$ have maximum degree at most $\Delta\ge2$, $0<\varepsilon<\tfrac12$, and $\delta=\varepsilon/32$, $\tau=\varepsilon/(64\Delta)$, $K=2^{\lceil\log_2(4096/\varepsilon^2)\rceil}$ as in (7.2). Let every vertex make $K$ independent proposals from a law $\tilde q\in Q$ with $P(\tilde q)\ge(2-\delta-2\Delta\tau)\nu_f(G)$ (the guarantee of Lemma 7.1 for the capped sampler), and let $S=\sum_v\min\{K,N_v\}$ count the kept proposals. Then the fractional matching of kept proposals satisfies
--   $$\Big(1-\frac\varepsilon{16}\Big)\nu_f(G)\le\frac{\mathbb ES}{2K}\le\nu_f(G).$$
--
--   Differences from the source:
--   - generalization: proposals drawn from the capped sampler law q̃ of §7.1 → proposals drawn from any q̃ ∈ Q with P(q̃) ≥ (2 − δ − 2Δτ)ν_f(G); reason: the capped law satisfies this bound by Lemma 7.1, so the item specializes to the source's statement; the proof uses only this bound
--   - encoding: E S → a finite sum over all proposal outcomes V × [K] → V ∪ {⊥} weighted by the product law; reason: finite probability space
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
--   - reading: G of maximum degree at most the degree bound ∆ used in τ = ε/(64∆) → G.degree v ≤ Δ for every v, with 2 ≤ Δ; reason: §2.1 standing assumption 'a known integer ∆ ≥ 2' bounding the maximum degree (p. 11), which (7.2) uses
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 40, Corollary 7.3

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Graph
import Definitions.Def_OptimalLCA_Matching_SaddlePoint
import Definitions.Def_OptimalLCA_Matching_Proposals

namespace OptimalLCA.Matching

/-- Corollary 7.3 (expected value), for proposals drawn independently from any law
`q̃ ∈ Q` with `P(q̃) ≥ (2 - δ - 2Δτ) ν_f(G)` (the guarantee of Lemma 7.1 for the capped
sampler), with `δ = ε/32`, `τ = ε/(64Δ)`, `K = 2^⌈log₂(4096/ε²)⌉`: the fractional matching
of kept proposals satisfies `(1 - ε/16) ν_f(G) ≤ E S / (2K) ≤ ν_f(G)`. -/
theorem corollary_7_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (q : Idx G → ℝ) (hq : InQ G q)
    (hP : (2 - paramDelta ε - 2 * (Δ : ℝ) * paramTau Δ ε) * fracMatchingNumber G ≤
      acceptedMass G q) :
    (1 - ε / 16) * fracMatchingNumber G ≤
        expectedKept G q (paramK ε) / (2 * (paramK ε : ℝ)) ∧
      expectedKept G q (paramK ε) / (2 * (paramK ε : ℝ)) ≤ fracMatchingNumber G := by sorry

end OptimalLCA.Matching
