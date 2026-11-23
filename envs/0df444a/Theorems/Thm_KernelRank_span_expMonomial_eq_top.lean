-- Prove2me | Theorems.Thm_KernelRank_span_expMonomial_eq_top
-- name    : KernelRank.span_expMonomial_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:16:31.093794+00:00
-- url     : https://prove2.me/theorems/5134c85d-b4e8-4c86-8098-ed2bdf010e0c
-- title:
--   Kernel Rank: span exp Monomial eq top
-- statement:
--   Exponential-monomial evaluation vectors `(s^q / q!) exp (rate i * s)` span
--   `∀ i, Fin (m₀ i) → ℂ` when `rate` is injective.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L922-L972
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L922-L972

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.span_expMonomial_eq_top {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (m₀ : ι → ℕ) :
    Submodule.span ℂ
      (Set.range fun s : ℝ≥0 => fun (i : ι) (q : Fin (m₀ i)) =>
        ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (s : ℂ))) = ⊤ := by sorry
