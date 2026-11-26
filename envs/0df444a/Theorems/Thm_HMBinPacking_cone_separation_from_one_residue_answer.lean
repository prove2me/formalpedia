-- Prove2me | Theorems.Thm_HMBinPacking_cone_separation_from_one_residue_answer
-- name    : HMBinPacking.cone_separation_from_one_residue_answer
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:12:36.863996+00:00
-- url     : https://prove2.me/theorems/388af703-8d04-556e-93bf-a9df5f1470d1
-- title:
--   Lemma 8, separation of a configuration cone from a single normalized query
-- statement:
--   For a high-multiplicity bin packing instance and residue $r$, let $P_r$ be the configuration polytope and $C_r$ its homogenized cone including the origin. Given a rational pair $(z,t)$, assume that when $t>0$ an answer to strong separation over $P_r$ at the single point $z/t$ is available. Then $(z,t)$ belongs to $C_r$, or there is a rational homogeneous linear functional that is nonpositive on all of $C_r$ and strictly positive at $(z,t)$. The statement includes the cases $t=0$, $t<0$, and $P_r$ empty.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 8, p.5. Geometric or encoding subclaim from the proof of Lemma 8.

import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
open HMBinPacking Finset

namespace HMBinPacking

theorem cone_separation_from_one_residue_answer (I : Instance) (r : Fin I.d → Fin I.d)
    (z : Fin I.d → ℚ) (t : ℚ)
    (oracle : 0 < t → ∃ w : List Bool, IsSepAnswer (Pr I r) (fun i => z i / t) w) :
    (qCast z, (t:ℝ)) ∈ Cr I r ∨
    ∃ (u : Fin I.d → ℚ) (a : ℚ),
      (∀ b ∈ Cr I r, (∑ i, (u i : ℝ) * b.1 i) + (a:ℝ) * b.2 ≤ 0) ∧
      0 < (∑ i, (u i : ℝ) * (z i:ℝ)) + (a:ℝ) * (t:ℝ) := by sorry

end HMBinPacking
