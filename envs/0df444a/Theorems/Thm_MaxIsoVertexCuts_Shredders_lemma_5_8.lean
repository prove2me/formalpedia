-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_5_8
-- name    : MaxIsoVertexCuts.Shredders.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:01:22.19322+00:00
-- url     : https://prove2.me/theorems/34654eb7-4e8d-4cab-a84e-75953e8568e0
-- title:
--   Lemma 5.8 — Merging L_i-complete certificates over a reconstructible representation certifies all c(G−S) components, in linear time
-- statement:
--   Let S be a shredder and (L_i,S,R_i) a reconstructible representation. Let Z be valid component certificates for S, such that every component D of every G[L_i] with |D|≤(2/3)|L_i| occurs in C of some L_i-complete certificate in Z. Then a complete certificate for S exists and can be computed by one deterministic RAM program in linear time in the total certificate input size. The program receives n and the certificates; the graph and reconstructible representation are not algorithmic advice. The output certifies exactly all c(G−S) components.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - encoding: linear time in certificate size → K times one plus the framed certificate input length, with the graph order supplied; reason: framing is linear in the stated certificate size; neither the graph nor target representations are supplied as an oracle
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 5.8, printed p.30 (PDF p.32)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_5_8 :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n) (cs : List (Cut n))
      (zs : List (Certificate n)), MergePremise G S cs zs → ∃ z, Complete G S z) ∧
    ∃ (P : CongruencyTU.Program) (K c : ℕ), 0 < K ∧ NoQueries P ∧ NoRandomness P ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n) (cs : List (Cut n))
        (zs : List (Certificate n)) (input : List ℤ),
        MergePremise G S cs zs → EncCollection (zs.map fun z => (S,z)) input →
        let B := K * (1 + input.length)
        let inp := (n : ℤ) :: input
        HaltWithin P CongruencyTU.noOracle CongruencyTU.noCoins inp B ∧
        WordBound P CongruencyTU.noOracle CongruencyTU.noCoins inp n input.length c ∧
        ∃ z, Complete G S z ∧ EncCert S z
          (CongruencyTU.outputAfter P CongruencyTU.noOracle CongruencyTU.noCoins inp B) := by sorry

end MaxIsoVertexCuts.Shredders
