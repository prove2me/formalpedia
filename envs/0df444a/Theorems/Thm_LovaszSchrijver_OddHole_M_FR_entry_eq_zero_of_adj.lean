-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_M_FR_entry_eq_zero_of_adj
-- name    : LovaszSchrijver.OddHole.M_FR_entry_eq_zero_of_adj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:48:34.31863+00:00
-- url     : https://prove2.me/theorems/4813e069-1d1e-4af0-adf3-1ccc3d93b498
-- title:
--   Section 2.b observation — Y ∈ M(FR(G)) has yᵢⱼ = 0 on edges
-- statement:
--   Let $G = (V, E)$ be a finite graph with no isolated nodes, and let $Y = (y_{ij})$ be a matrix in $M(\mathrm{FR}(G)) = M(\mathrm{FR}(G), Q)$, with rows and columns indexed by $V \cup \{0\}$. Then
--   $$y_{ij} = 0 \quad \text{whenever } ij \in E(G).$$
--
--   The observation says that the lifted matrices of one round of $N$ carry no mass on the edges of the graph, which is what makes the system in part (2) of the proof of Theorem 2.3 a system in two variables per inequality.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 177, Section 2.b

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones

namespace LovaszSchrijver.OddHole

/-- Section 2.b, p. 177: if `Y = (yᵢⱼ) ∈ M(FR(G))` then `yᵢⱼ = 0` whenever `ij ∈ E(G)`. -/
theorem M_FR_entry_eq_zero_of_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (Y : Matrix (Option V) (Option V) ℝ) (hY : Y ∈ M (FR G) (Q V))
    (i j : V) (hij : G.Adj i j) :
    Y (some i) (some j) = 0 := by sorry

end LovaszSchrijver.OddHole
