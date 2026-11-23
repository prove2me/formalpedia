-- Prove2me | Theorems.Thm_KernelRank_coeff_eq_sum_rootsOfUnity
-- name    : KernelRank.coeff_eq_sum_rootsOfUnity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:12:52.022431+00:00
-- url     : https://prove2.me/theorems/7da25c75-f666-43c4-bd2d-4cb147de3b32
-- title:
--   Kernel Rank: coeff eq sum roots Of Unity
-- statement:
--   Extracting the `k`-th coefficient of a polynomial `Q ∈ ℂ[X]` of degree `< k + L` (with
--   `k < L`) by averaging `ζ ^ (-k r) · Q(ζ ^ r)` over the `L`-th roots of unity.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L30-L110
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L30-L110

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.coeff_eq_sum_rootsOfUnity (Q : ℂ[X]) {k L : ℕ} (hkL : k < L)
    (hdeg : Q.natDegree < k + L) :
    Q.coeff k = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L,
      exp (-2 * Real.pi * I * k * r / L) * Q.eval (exp (2 * Real.pi * I * r / L)) := by sorry
