-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_theorem_4_9
-- name    : LinearSetReconciliation327.Main.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:44.083254+00:00
-- url     : https://prove2.me/theorems/1383ee93-b312-46f2-b0a3-0833a81bb117
-- title:
--   Theorem 4.9 — Recovery from capacity bounds
-- statement:
--   For a well-formed sketch tree over a CR family that recovers every vector within capacity, and a valid root input $x$ and hint $J$ with capacities $(X,Y)$: (i) on every seed for which $U_s\le X_s$, $V_s\le Y_s$, $Z\le t$ hold at every node of the exact execution, the real decoder returns $x$ from the stored vector and $J$; (ii) if for every node, and every input and hint valid at that node, each bound fails with probability at most $\delta$ over the node's own randomness, the decoder fails with probability at most $Q\delta$, where $Q$ counts all bounds in the tree. Hints go only to the decoder.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - generalization: a node of the top layer or of HintSketch → any RowScheme: any row code, prediction and final-recovery procedures; reason: the proof uses only that a row reads its local support, local hint and coins; both constructions are RowSchemes, so the source claim is an instance
--   - encoding: root condition ‖x‖₀ ≤ d, hint if present → Problem 3.1 validity for the root capacities (X, Y), where an unhinted root has J = ∅, X = 0, Y = d; reason: footnote 4 sets J = ∅ at the top layer, so the root conditions coincide
--   - encoding: CR sketch of Proposition 2.3 → a CR family with the recovery property as hypothesis; reason: the proof uses only recovery within capacity; Proposition 2.3 supplies the family
--   - reading: each bound fails with probability at most δ → for every node and every input and hint valid there, over the node own randomness; reason: the source proof conditions on ancestors and applies the bound at the resulting node input
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 4.9, PDF p.18 (printed p.17)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Theorem 4.9 (Recovery from capacity bounds), PDF p.18 (printed p.17), for a tree of any row
schemes. The CR family recovers, as Proposition 2.3 states. -/
theorem theorem_4_9 (CR : CRFamily) (hCR : CR.Recovers) (T : Node) (X Y : ℕ) (hT : T.WF X Y)
    (x J : Finset ℕ) (hvalid : Node.Valid T.N X Y x J) :
    (∀ r : T.Seed, T.AllBounds r x J → T.decode CR r (T.sketch CR r x) J = some x) ∧
    (∀ δ : ℝ, T.BoundsProb δ X Y →
      prU (fun r : T.Seed => T.decode CR r (T.sketch CR r x) J ≠ some x) ≤
        (T.boundCount : ℝ) * δ) := by sorry

end LinearSetReconciliation327.Main
