-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_proposition_3_3
-- name    : MaxIsoVertexCuts.Shredders.proposition_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:00:36.627711+00:00
-- url     : https://prove2.me/theorems/4594ff8f-9400-44d9-a9e6-90296ade0b5a
-- title:
--   Proposition 3.3 — Weighted Jackson–Jordán inequalities for f(X)=w(N(X)): submodularity and the N[·]-posimodularity
-- statement:
--   For a finite simple graph with strictly positive real vertex weights, put f(X)=w(N(X)), where N excludes X, and X*=V−N[X]. For all X,Y, f(X∩Y)+f(X∪Y)≤f(X)+f(Y), and f(X∩Y*)+f(Y∩X*)≤f(X)+f(Y). The latter sum equals f(X−N[Y])+f(Y−N[X]).
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Proposition 3.3, printed p.17 (PDF p.19)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem proposition_3_3 {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (X Y : VSet n) :
    boundaryWeight G w (X ∩ Y) + boundaryWeight G w (X ∪ Y) ≤
      boundaryWeight G w X + boundaryWeight G w Y ∧
    boundaryWeight G w (X ∩ exterior G Y) + boundaryWeight G w (Y ∩ exterior G X) ≤
      boundaryWeight G w X + boundaryWeight G w Y ∧
    boundaryWeight G w (X ∩ exterior G Y) + boundaryWeight G w (Y ∩ exterior G X) =
      boundaryWeight G w (X \ closedNbhd G Y) + boundaryWeight G w (Y \ closedNbhd G X) := by sorry

end MaxIsoVertexCuts.Shredders
