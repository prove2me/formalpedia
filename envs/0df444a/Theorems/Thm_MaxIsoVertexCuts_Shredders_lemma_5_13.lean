-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_5_13
-- name    : MaxIsoVertexCuts.Shredders.lemma_5_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:01:05.16174+00:00
-- url     : https://prove2.me/theorems/1b0211bc-3743-44bb-bc16-6854fb2f6a42
-- title:
--   Lemma 5.13 — Weighted U-Steiner s-t-shredder listing with component certificates in max-flow time
-- statement:
--   For each fixed polynomial weight exponent, a deterministic max-flow reduction takes a connected positively integer-weighted graph, U⊆V and s,t∈U. It always returns valid Steiner component certificates for genuine U-Steiner minimum s-t shredders, in O(T_MaxFlow(m,n)) time and O(m) total output size. If κ_G(s,t)=κ_G(U), every U-Steiner s-t shredder has a complete returned certificate. Both connectivities can be infinite; no separability or distinctness hypothesis is imposed. When s=t there are no source-sink shredders.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - encoding: connected simple algorithm inputs by the standing assumption on printed p.16 → GraphData.Valid and an explicit duplicate-free edge list; reason: exactly the source algorithmic domain and its finite input representation
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - reading: positive polynomially bounded weights → positive integral weights bounded by n^d, with d fixed before the program and input; reason: the integer-machine reading agrees with the paper’s polynomially bounded integral element-weight convention
--   - reading: time T_MaxFlow(m,n) for a maximum vertex-capacitated flow → uniform reduction to every integral maximum vertex-flow oracle and every monotone jointly superadditive T≥m+n; reason: states the black-box meaning of the max-flow bound, without requiring cycle-free answers
--   - encoding: possibly infinite source-sink and Steiner connectivities → ENNReal infima; infinity for the empty feasible family; reason: retains inseparable, coincident and adjacent-terminal cases; when s=t there are no source-sink separators, matching the outsider routine’s explicit empty-output case
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 5.13, printed p.32 (PDF p.34)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_5_13 : ∀ d : ℕ, ∃ (P : CongruencyTU.Program) (K c : ℕ), 0 < K ∧
    NoRandomness P ∧ ∀ O, IsVertexFlowOracle O → ∀ time, AdmissibleTime time →
    ∀ (I : GraphData) (w : Fin I.n → ℕ) (U : VSet I.n) (s t : Fin I.n),
      I.Valid → BoundedWeights I d w → s ∈ U → t ∈ U →
      OracleRun P O (encTerminals I w U ++ [(s.val : ℤ), (t.val : ℤ)]) time
        (K * time I.m I.n) I.n I.m c
        (fun out => stOutput I w U s t out ∧ out.length ≤ K * I.m) := by sorry

end MaxIsoVertexCuts.Shredders
