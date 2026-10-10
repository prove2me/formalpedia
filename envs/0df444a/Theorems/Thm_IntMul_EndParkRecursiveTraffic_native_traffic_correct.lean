-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveTraffic_native_traffic_correct
-- name    : IntMul.EndParkRecursiveTraffic.native_traffic_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T04:45:56.388977+00:00
-- url     : https://prove2.me/theorems/df56b40a-bc7c-4f02-b592-3be34022ea13
-- title:
--   Literal recursive machine clock from actual word and reservation-movement traffic
-- statement:
--   A finite recursive computation certificate counts actual ordinary body transitions S and an additive local word-space traffic V over the complete call tree. One fixed selective-return scheduler using exactly M.k+3 tapes physically executes it from ordinary native input to its exact final configuration and canonical output in at most S+32V+5|x#y|+4|w|+18 actual transitions. Each return contributes its retained span, shared/result lengths and one unit to V. Each call contributes the current result-head position, ACTUAL fresh-bank reservation distance after packet extraction, shared word, argument packet, child result, fixed finite label count and one unit. Unchanged parent banks whose heads are already parked contribute zero to reservation distance. No offset, depth or unseen tape movement enters the clock or machine control. The theorem converts spatial/traffic accounting into an actual machine bound; a fast body and an appropriately small total traffic still have to be supplied.
-- source:
--   Original additive-traffic to actual fixed-tape native-clock theorem for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveTraffic
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_evaluates_correct
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveTraffic IntMul.EndParkRecursiveScheduler IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveTraffic.native_traffic_correct (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (x y w : List Bool) (steps mass : ℕ)
    (traffic : HasTraffic M labels request resume (initialExtent M x y) (M.initCfg x y) [] w steps mass) :
    ∃ t, t ≤ steps+32*mass+5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M labels request resume).step^[t] ((machine M labels request resume).initCfg x y)=
        nativeFinalFrame M labels request resume x y w ∧
      (machine M labels request resume).HaltsWithOutput x y t w := by sorry
