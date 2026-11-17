-- Prove2me | Theorems.Thm_MazurProof_TateNormalFormBridge_exists_tate_normalized_of_addOrder_gt_three
-- name    : MazurProof.TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:32.381936+00:00
-- url     : https://prove2.me/theorems/6fac96ac-5329-40f4-a241-300e65ef38e9
-- title:
--   Every rational point of order greater than three admits Tate normal form
-- statement:
--   Let $E/ℚ$ be an elliptic curve, let $P∈E(ℚ)$ have exact additive order $n>3$. Then there exist $b,c∈ℚ$ such that the Tate normal-form curve $W(b,c)$ is elliptic, its distinguished origin has exact order $n$, and $$b≠0.$$ This supplies the coordinate normalization used to derive explicit division-polynomial conditions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_TateNormalFormBridge
import Definitions.Def_TateZ2xZ10Reduction

open scoped WeierstrassCurve.Affine
open MazurProof
open MazurProof.TateNormalFormBridge
open Scratch.TateZ2xZ10Reduction

theorem MazurProof.TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 := by sorry
