-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_5_18
-- name    : MaxIsoVertexCuts.Shredders.lemma_5_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:59:51.912519+00:00
-- url     : https://prove2.me/theorems/932bd192-257f-428a-adcd-5a2489957a5c
-- title:
--   Lemma 5.18 — ℓ-linked case: certificates for target cuts with |S| ≥ 20|L|·4^{log^{0.7} n}
-- statement:
--   For every confidence exponent a≥1 there is one randomized program taking a connected graph and integers κ_G≤k≤δ_G and ℓ, running in worst-case m^(1+o(1)) time and always outputting valid certificates of genuine k-shredders. For every fixed choice of reconstructible representations, if k=κ_G, with probability at least 1−n^(−a), simultaneously for every target cut (L,S,R) with ℓ/2≤|L|≤ℓ, L ℓ-linked and |S|≥20|L|·4^((log₂n)^0.7), and every component D of G[L] with |D|≤(2/3)|L|, a returned L-complete certificate has D in its component collection. Linkedness means some s∈S has |N(s)∩R|≤2ℓ·2^((log₂n)^0.7).
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - encoding: connected simple algorithm inputs by the standing assumption on printed p.16 → GraphData.Valid and an explicit duplicate-free edge list; reason: exactly the source algorithmic domain and its finite input representation
--   - reading: algorithmic time without an explicit machine → the published integer RAM with O(log(n+m))-bit words and charged explicit output; reason: fixes the computational model without granting an algorithm or a runtime as input
--   - reading: with high probability and m^(1+o(1)) → for every a≥1 one program works for all ε>0 with success at least 1−n^(−a) and time K(m+2)^(1+ε); reason: the paper permits tunable repetition constants and a subpolynomial factor
--   - encoding: asymptotic time m^(1+o(1)) → ceil(K(m+2)^(1+ε)); reason: the harmless shift and integer ceiling cover zero- and one-edge inputs
--   - reading: minimum vertex-separator size, with no complete-graph value specified → κ(K_n)=n−1 and no shredders in complete graphs; reason: standard connectivity convention consistent with k in [κ,δ] in the proof
--   - encoding: any integer ℓ and fixed target cuts → ℓ an integer (ℤ), clamped to [0, 2n+1] in the input; every fixed reconstructible-representation choice is outside the success fraction; reason: for ℓ ≤ 0 and ℓ > 2n the target window is empty (a target cut has 1 ≤ |L| ≤ n), so the clamp changes no guarantee, and success covers all qualifying cuts and components jointly
--   - encoding: separators and component lists stored once and referenced across certificates (printed pp.28,39–41) → serialized separator and component-list dictionaries with an index pair and witness list per certificate; reason: retains the source runtime for many certificates of one shredder; the final goal still uses explicit output lists
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 5.18, printed p.35 (PDF p.37)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_5_18 : CollectionAlgorithm true := by sorry

end MaxIsoVertexCuts.Shredders
