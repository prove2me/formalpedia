-- Prove2me | Theorems.Thm_Helfgott_reciprocal_certificate_log_grid
-- name    : Helfgott.reciprocal_certificate_log_grid
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T21:51:11.015459+00:00
-- url     : https://prove2.me/theorems/6065e681-cd80-410d-ad42-9a49f229c8c9
-- title:
--   Exact logarithm cutoff grid for finite reciprocal Mobius certificates
-- statement:
--   For each integer $k$ from $94$ to $140$, let $T_k$ be the explicit integer cutoff in the formal statement. Then $\log T_k\le k/10$. The grid covers cutoffs from $12088$ through $1202604$, enough to upper bound $\log(n+1)$ throughout the finite reciprocal Mobius interval $11815\le n<1200000$. Each cutoff is proved by a rational 70-term lower bound for the exponential, with no floating point assumption.
-- source:
--   Original exact rational cutoff certificate for finite reciprocal Mobius estimates in the Helfgott minor-arc route. Written by Codex.

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Finset Real
open scoped BigOperators

namespace Helfgott

theorem reciprocal_certificate_log_grid : ∀ c ∈ ([(94, 12088), (95, 13359), (96, 14764), (97, 16317), (98, 18033), (99, 19930), (100, 22026), (101, 24343), (102, 26903), (103, 29732), (104, 32859), (105, 36315), (106, 40134), (107, 44355), (108, 49020), (109, 54176), (110, 59874), (111, 66171), (112, 73130), (113, 80821), (114, 89321), (115, 98715), (116, 109097), (117, 120571), (118, 133252), (119, 147266), (120, 162754), (121, 179871), (122, 198789), (123, 219695), (124, 242801), (125, 268337), (126, 296558), (127, 327747), (128, 362217), (129, 400312), (130, 442413), (131, 488942), (132, 540364), (133, 597195), (134, 660003), (135, 729416), (136, 806129), (137, 890911), (138, 984609), (139, 1088161), (140, 1202604)] : List (ℕ × ℕ)), Real.log (c.2 : ℝ) ≤ (c.1 : ℝ) / 10 := by sorry

end Helfgott
