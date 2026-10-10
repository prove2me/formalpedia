-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveTraffic_kappa_bound_of_traffic
-- name    : IntMul.EndParkRecursiveTraffic.kappa_bound_of_traffic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T04:41:37.619924+00:00
-- url     : https://prove2.me/theorems/51e42536-8085-4e77-8d24-cb0056b7fabc
-- title:
--   Exact campaign kappa bound from total optimized recursive traffic certificates
-- statement:
--   For one fixed finite body, request map and continuation map, pointwise finite multiplication traffic certificates for all positive input sizes and an eventual bound S+32V ≤ C n lg(n)^(1−κ) imply the campaign's exact KappaBound κ predicate, for κ ≤ 1. The witness is the single complete optimized recursive machine with exactly M.k+3 tapes, actual native input and canonical product output. S counts ordinary body transitions; V counts actual reservation movement and word traffic, excluding untouched parked parent banks. The compiler adds only 18n+23 native transitions, absorbed into a fixed constant. Finite pointwise totality implies a uniform bound at each size by finiteness of bit-word inputs. The fast body and total-traffic bound are explicit premises and are not supplied here.
-- source:
--   Original exact KappaBound compiler interface using tight recursive movement traffic. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveTraffic
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_evaluates_correct
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveTraffic IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveTraffic.kappa_bound_of_traffic (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ ≤ 1)
    (total : ∀ width : ℕ, 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps mass : ℕ, HasTraffic M labels request resume (initialExtent M x y)
          (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass)
    (C : ℝ) (hC : 0 < C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold ≤ width → 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps mass : ℕ, ((steps+32*mass:ℕ):ℝ) ≤ C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          HasTraffic M labels request resume (initialExtent M x y)
            (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps mass) :
    KappaBound κ := by sorry
