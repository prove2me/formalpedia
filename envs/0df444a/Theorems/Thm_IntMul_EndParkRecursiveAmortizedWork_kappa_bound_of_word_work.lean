-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveAmortizedWork_kappa_bound_of_word_work
-- name    : IntMul.EndParkRecursiveAmortizedWork.kappa_bound_of_word_work
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:01:23.991066+00:00
-- url     : https://prove2.me/theorems/4ca1e19e-e71d-4786-8923-dc13a38d15ad
-- title:
--   Exact campaign kappa bound from body steps and recursive word lengths alone
-- statement:
--   For one fixed finite recursive multiplication body, fixed request/resume maps, pointwise total word-work certificates for all positive widths, and an eventual bound S+32(W+(2k+3)S) ≤ C n lg(n)^(1−κ), the exact campaign KappaBound κ predicate follows for κ ≤ 1. The fixed tape count is k, S counts actual ordinary body transitions and W is an additive simple argument/shared/result word charge over the call tree. Retained extents and head distances are discharged by amortization rather than appearing in the fast-cost premise. The witness is one complete optimized native fixed-tape machine. A fast body and that total word-work estimate remain explicit premises.
-- source:
--   Original amortized word-work to exact KappaBound compiler interface. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveAmortizedWork
import Theorems.Thm_IntMul_EndParkRecursiveTraffic_kappa_bound_of_traffic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveAmortizedWork IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveAmortizedWork.kappa_bound_of_word_work (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ≤ 1)
    (total : ∀ width : ℕ, 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps work : ℕ, HasWordWork M labels request resume (initialExtent M x y)
          (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps work)
    (C : ℝ) (hC : 0< C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold≤ width → 1≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ steps work : ℕ, ((steps+32*(work+(2*M.k+3)*steps):ℕ):ℝ)≤
          C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          HasWordWork M labels request resume (initialExtent M x y)
            (M.initCfg x y) [] (bin (2*width) (val x*val y)) steps work) :
    KappaBound κ := by sorry
