-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_2_1
-- name    : MildHamilton.Main.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:28.067839+00:00
-- url     : https://prove2.me/theorems/da80c8d6-d998-47b7-8df8-a9e8da15f9ef
-- title:
--   Lemma 2.1, p. 3 — a spectral gap gives cut density
-- statement:
--   Let $G$ be a graph on $n\ge2$ vertices, with minimum degree $\delta(G)$, and let $\lambda_2(G)$ be the second largest eigenvalue of its adjacency matrix, counted with multiplicity. If $\delta(G)>\lambda_2(G)$, then $G$ is
--
--   $$\frac{\delta(G)-\lambda_2(G)}{n}\text{-cut-dense}.$$
--
--   This translates a spectral bound into a combinatorial expansion property, and is applied to the random bipartite graphs of the final proof.
--
--   Differences from the source: none.
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 2.1, p. 3

import Mathlib
import Definitions.Def_MildHamilton_Main_Spectral

namespace MildHamilton.Main

/-- Lemma 2.1 (Muyesser, STOC 2027 submission #233, p. 3): spectral gap gives cut density. -/
theorem lemma_2_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 1 < Fintype.card V)
    (hgap : adjEigenvalues G ⟨1, hn⟩ < (G.minDegree : ℝ)) :
    IsCutDense G (((G.minDegree : ℝ) - adjEigenvalues G ⟨1, hn⟩) / (Fintype.card V : ℝ)) := by sorry

end MildHamilton.Main
