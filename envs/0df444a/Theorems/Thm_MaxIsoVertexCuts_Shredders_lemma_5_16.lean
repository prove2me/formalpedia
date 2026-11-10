-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_5_16
-- name    : MaxIsoVertexCuts.Shredders.lemma_5_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:59:35.098021+00:00
-- url     : https://prove2.me/theorems/35b3efc3-7eb7-48d0-a6cc-1c648764b3b7
-- title:
--   Lemma 5.16 — t-isolating U-Steiner shredders of weight k for all t ∈ T with T-terminal-complete certificates
-- statement:
--   For each fixed polynomial weight exponent there is a deterministic max-flow reduction taking a connected positively integer-weighted graph, T⊆U⊆V with T independent and |T|≥2, and an integer k. For each t∈T it returns certificates for t-isolating U-Steiner shredders of weight k. Each certificate is (C,{t,t′}) for some t′∈T−{t}, and every component in C misses T. Running time is O(log|T|·T_MaxFlow(m,m)), and total encoded output size is O(m), using shared separator and component-list dictionaries as the source permits. If k=κ_G(U), every such shredder for every t has a T-terminal-complete returned certificate. Guarantees are uniform over every correct max-flow oracle and admissible time function.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - encoding: connected simple algorithm inputs by the standing assumption on printed p.16 → GraphData.Valid and an explicit duplicate-free edge list; reason: exactly the source algorithmic domain and its finite input representation
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - reading: positive polynomially bounded weights → positive integral weights bounded by n^d, with d fixed before the program and input; reason: the integer-machine reading agrees with the paper’s polynomially bounded integral element-weight convention
--   - reading: time T_MaxFlow(m,n) for a maximum vertex-capacitated flow → uniform reduction to every integral maximum vertex-flow oracle and every monotone jointly superadditive T≥m+n; reason: states the black-box meaning of the max-flow bound, without requiring cycle-free answers
--   - encoding: parameter k and logarithmic terminal factor → integer k, saturated to [−1,total vertex weight+1] in the input; max(1,ceil(log₂|T|)); reason: positive integral weights have no negative or over-total-weight separators; saturation retains those empty cases, while rounding only changes the time constant
--   - encoding: separator and component lists shared by reference (printed pp.28,34) → explicitly serialized shared dictionaries with bounded indices in each terminal row; reason: preserves the source O(m) output-size clause instead of charging repeated copies
--   - reading: a parameter k for integral-weight algorithmic inputs → an arbitrary integer k; reason: the integer-machine convention for a requested separator weight; all negative and over-total-weight values are retained
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 5.16, printed p.32 (PDF p.34)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_5_16 : ∀ d : ℕ, ∃ (P : CongruencyTU.Program) (K c : ℕ), 0 < K ∧
    NoRandomness P ∧ ∀ O, IsVertexFlowOracle O → ∀ time, AdmissibleTime time →
    ∀ (I : GraphData) (w : Fin I.n → ℕ) (U T : VSet I.n) (k : ℤ),
      I.Valid → BoundedWeights I d w → T ⊆ U → Independent I.G T → 2 ≤ T.card →
      OracleRun P O
        (encTerminals I w U ++ CongruencyTU.pack [encSet T] ++
          [min (max k (-1)) ((∑ v, (w v : ℤ))+1)]) time
        (K * logarithmicFactor T * time I.m I.m) I.n I.m c
        (fun out => isolatingSteinerOutput I w U T k out ∧ out.length ≤ K * I.m) := by sorry

end MaxIsoVertexCuts.Shredders
