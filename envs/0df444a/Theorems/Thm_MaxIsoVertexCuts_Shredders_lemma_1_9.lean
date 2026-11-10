-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_1_9
-- name    : MaxIsoVertexCuts.Shredders.lemma_1_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:59:34.529375+00:00
-- url     : https://prove2.me/theorems/c06d8180-71ad-41b5-997d-3568241e6361
-- title:
--   Lemma 1.9 — Maximal isolating vertex cuts for all terminals in O(log|T|·T_MaxFlow(m,m)) time, total output O(m)
-- statement:
--   For every fixed polynomial weight exponent there is a deterministic program, uniformly over correct max-flow oracles and admissible time functions, that for each connected simple positively integer-weighted graph and independent terminal set T with |T|≥2 returns, for every t∈T, the maximal minimum (t,T−{t}) separator S_t, shore L_t, and all graph edges with at least one endpoint in L_t. Total output length is O(m) and running time is O(log|T|·T_MaxFlow(m,m)).
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - encoding: connected simple algorithm inputs by the standing assumption on printed p.16 → GraphData.Valid and an explicit duplicate-free edge list; reason: exactly the source algorithmic domain and its finite input representation
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - reading: positive polynomially bounded weights → positive integral weights bounded by n^d, with d fixed before the program and input; reason: the integer-machine reading agrees with the paper’s polynomially bounded integral element-weight convention
--   - reading: time T_MaxFlow(m,n) for a maximum vertex-capacitated flow → uniform reduction to every integral maximum vertex-flow oracle and every monotone jointly superadditive T≥m+n; reason: states the black-box meaning of the max-flow bound, without requiring cycle-free answers
--   - encoding: isolating cuts (t,T−{t}) and log|T| → 2≤|T| and max(1,ceil(log₂|T|)); reason: the source skips smaller terminal samples, whose cuts are undefined; rounding changes only the absolute time constant
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 1.9, printed p.9 (PDF p.11)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_1_9 : ∀ d : ℕ, ∃ (P : CongruencyTU.Program) (K c : ℕ), 0 < K ∧
    NoRandomness P ∧ ∀ O, IsVertexFlowOracle O → ∀ time, AdmissibleTime time →
    ∀ (I : GraphData) (w : Fin I.n → ℕ) (T : VSet I.n),
      I.Valid → BoundedWeights I d w → Independent I.G T → 2 ≤ T.card →
      OracleRun P O (encTerminals I w T) time
        (K * logarithmicFactor T * time I.m I.m) I.n I.m c
        (fun out => isolatingOutput I w T out ∧ out.length ≤ K * I.m) := by sorry

end MaxIsoVertexCuts.Shredders
