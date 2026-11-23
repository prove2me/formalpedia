-- Prove2me | Theorems.Thm_KernelRank_span_realExpEval_eq_top
-- name    : KernelRank.span_realExpEval_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:20:41.944478+00:00
-- url     : https://prove2.me/theorems/c5b2c921-01b2-4666-a263-fd6078604fe7
-- title:
--   Kernel Rank: span real Exp Eval eq top
-- statement:
--   Exponential-monomial evaluation vectors span `RealExpSpace m_R m_C` over `ℝ` when `rate` is
--   injective and lies in the closed upper half-plane.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2237-L2411
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2237-L2411

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
open scoped Classical

theorem KernelRank.span_realExpEval_eq_top {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) (m : ι → ℕ) :
    Submodule.span ℝ
      (Set.range fun s : ℝ≥0 =>
        ((fun (i : {i : ι // (rate i).im = 0}) (q : Fin (m i.1)) =>
            ((s : ℝ) ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) *
              Real.exp ((rate i.1).re * (s : ℝ))),
         (fun (k : {i : ι // 0 < (rate i).im}) (q : Fin (m k.1)) =>
            ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
              exp (rate k.1 * (s : ℂ))))) = ⊤ := by sorry
