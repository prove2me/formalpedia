-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_theorem_1_2
-- name    : MaxIsoVertexCuts.Shredders.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:00:37.25078+00:00
-- url     : https://prove2.me/theorems/f97a165f-4953-4757-a40e-2ceb9d6973db
-- title:
--   Theorem 1.2 — Almost-linear listing of all minimum vertex-cut shredders
-- statement:
--   For every a≥1 there is one randomized RAM program, with no oracle, which on every connected simple graph with n vertices and m edges always halts in time m^(1+o(1)) and returns an integer k and a collection of genuine k-shredders with valid component certificates. On one event of probability at least 1−n^(−a), k=κ_G, the returned separators are exactly all κ_G-shredders, and every returned certificate is complete. The same program works for every ε>0: for some input-independent K, all executions take at most ceil(K(m+2)^(1+ε)) instructions including explicit output-writing cost, with O(log(n+m))-bit words. Maximum flow, connectivity and clustering are solver obligations, not supplied oracles.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - encoding: connected simple algorithm inputs by the standing assumption on printed p.16 → GraphData.Valid and an explicit duplicate-free edge list; reason: exactly the source algorithmic domain and its finite input representation
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - reading: with high probability and m^(1+o(1)) → for every a≥1 one program works for all ε>0 with success at least 1−n^(−a) and time K(m+2)^(1+ε); reason: the paper permits tunable repetition constants and a subpolynomial factor
--   - encoding: asymptotic time m^(1+o(1)) → ceil(K(m+2)^(1+ε)); reason: the harmless shift and integer ceiling cover zero- and one-edge inputs
--   - reading: minimum vertex-separator size, with no complete-graph value specified → κ(K_n)=n−1 and no shredders in complete graphs; reason: standard connectivity convention consistent with k in [κ,δ] in the proof
--   - encoding: returned integer k, lying in [κ,δ] in the proof → a natural k serialized as an integer; reason: the algorithm in the proof already returns a nonnegative cut-size estimate
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Theorem 1.2, printed p.3 (PDF p.5)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem theorem_1_2 : ∀ a : ℝ, 1 ≤ a →
    ∃ (P : CongruencyTU.Program) (c : ℕ), NoQueries P ∧
      ∀ eps : ℝ, 0 < eps → ∃ K : ℝ, 0 < K ∧ ∀ I : GraphData, I.Valid →
        let B := almostLinearBudget K eps I.m
        (∀ coins : Fin B → Bool,
          HaltWithin P CongruencyTU.noOracle (CongruencyTU.extendCoins coins) I.encode B ∧
          WordBound P CongruencyTU.noOracle (CongruencyTU.extendCoins coins) I.encode I.n I.m c ∧
          listingValid I (CongruencyTU.outputAfter P CongruencyTU.noOracle
            (CongruencyTU.extendCoins coins) I.encode B)) ∧
        1 - (I.n : ℝ)^(-a) ≤ successFraction P I.encode B (listingComplete I) := by sorry

end MaxIsoVertexCuts.Shredders
