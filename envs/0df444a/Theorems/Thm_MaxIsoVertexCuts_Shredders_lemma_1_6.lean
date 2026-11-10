-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_1_6
-- name    : MaxIsoVertexCuts.Shredders.lemma_1_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:00:56.087951+00:00
-- url     : https://prove2.me/theorems/671be665-2e6b-4502-b7dc-ffedcfb4eced
-- title:
--   Lemma 1.6 — Weighted s-t-outsider oracle in one max-flow time
-- statement:
--   For each fixed polynomial weight exponent d, there is one deterministic RAM program, with uniform constants, that for every connected simple graph with positive integer weights w(v)≤n^d and vertices s,t, returns exactly the s-t-outsiders in O(T_MaxFlow(m,n)) time. This holds for every correct vertex-capacitated maximum-flow oracle and every admissible time function T. A correct oracle may return a maximum flow with circulations. Coincident and adjacent terminals are retained and have no outsiders, as the proof specifies on printed p.21. The cycle-free-flow proof gap is recorded as insight I1.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - encoding: connected simple algorithm inputs by the standing assumption on printed p.16 → GraphData.Valid and an explicit duplicate-free edge list; reason: exactly the source algorithmic domain and its finite input representation
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - reading: positive polynomially bounded weights → positive integral weights bounded by n^d, with d fixed before the program and input; reason: the integer-machine reading agrees with the paper’s polynomially bounded integral element-weight convention
--   - reading: time T_MaxFlow(m,n) for a maximum vertex-capacitated flow → uniform reduction to every integral maximum vertex-flow oracle and every monotone jointly superadditive T≥m+n; reason: states the black-box meaning of the max-flow bound, without requiring cycle-free answers
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 1.6, printed p.5 (PDF p.7)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_1_6 : ∀ d : ℕ, ∃ (P : CongruencyTU.Program) (K c : ℕ), 0 < K ∧
    NoRandomness P ∧ ∀ O, IsVertexFlowOracle O → ∀ T, AdmissibleTime T →
    ∀ (I : GraphData) (w : Fin I.n → ℕ) (s t : Fin I.n),
      I.Valid → BoundedWeights I d w →
      OracleRun P O (encWeighted I w ++ [(s.val : ℤ), (t.val : ℤ)]) T
        (K * T I.m I.n) I.n I.m c
        (fun out => ∃ xs : List (Fin I.n), xs.Nodup ∧
          xs.toFinset = outsiders I.G (realWeights w) {s,t} {s} ∧
          out = xs.map fun v => (v.val : ℤ)) := by sorry

end MaxIsoVertexCuts.Shredders
