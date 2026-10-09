-- Prove2me | Theorems.Thm_NicerEars_TwoEC_claim_p23
-- name    : NicerEars.TwoEC.claim_p23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:40.561384+00:00
-- url     : https://prove2.me/theorems/0a3445ca-9488-4018-be7f-a763ab520a3d
-- title:
--   Proof of Theorem 30, Claim, p. 23 — the nontrivial ears form a 2ECSS with at most 5/4 L_ϕ(G) + ½π edges
-- statement:
--   Let $G$ be a graph with a nice ear-decomposition, and let $\pi$ be its number of pendant ears. Let $F$ be the union of the edge sets of the nontrivial ears (ears of length at least 2). Then $F$ spans a 2-edge-connected subgraph of $G$, and
--
--   $$|F|\le\tfrac54L_\varphi(G)+\tfrac12\pi,\qquad L_\varphi(G)=|V(G)|+\varphi(G)-1 .$$
--
--   This is the second construction for 2ECSS, used when there are few pendant ears.
--
--   **Formalization Note** That $F$ is a 2ECSS is the paper's remark on p. 6 that deleting 1-ears maintains 2-edge-connectivity, which the proof of Theorem 30 uses; it is stated as the first conjunct. The Claim is stated in the proof of Theorem 30 for the decomposition of Lemma 23 with $T=\emptyset$; only niceness enters its proof (the even ears number $\varphi(G)$, and every 3-ear is pendant), so only niceness is assumed.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 23, proof of Theorem 30, Claim; p. 6, "deleting 1-ears maintains 2-edge-connectivity"

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

namespace NicerEars.TwoEC

open Finset

theorem claim_p23 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (D : EarDecomposition G) (hD : D.IsNice) :
    G.IsTwoECSpanning D.nontrivialEdges ∧
      (#D.nontrivialEdges : ℝ) ≤ 5 / 4 * (Lphi G : ℝ) + 1 / 2 * D.numPendant := by sorry

end NicerEars.TwoEC
