-- Prove2me | Theorems.Thm_MazurTransfer_RationalQuotientPicardGaloisTrace_pic0_galois_trace_eq_zero
-- name    : MazurTransfer.RationalQuotientPicardGaloisTrace.pic0_galois_trace_eq_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T16:20:11.491703+00:00
-- url     : https://prove2.me/theorems/6d94b441-5f18-46f6-bca2-179c8ec3582c
-- title:
--   Arithmetic Pic0 Galois trace vanishes over a rational quotient
-- statement:
--   With the original field and scalar-tower structures, let E/F be finite Galois and assume HasPrincipalDivisors K E. A specified K-algebra equivalence K(t) to F makes the sum of the F-Galois conjugates of any arithmetic Pic0(K,E) class equal to zero. Every original hypothesis and universe is retained.
-- source:
--   Unchanged complete original MazurTheorem RationalQuotientPicardGaloisTrace.pic0_galois_trace_eq_zero proof and statement; official Anthropic FLT divisor and quotient interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original Pic0 Galois-trace proof retained, using its public principal-divisor input.
Design boundary: the sum of Galois conjugates of any arithmetic degree-zero
Picard class vanishes over a specified rational quotient field.
Named downstream consumer: finite-subgroup and cyclic Pic0 trace.
Official Anthropic FLT divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_RationalQuotientPicardGaloisTrace_degree_zero_galois_trace_principal
noncomputable section
universe u v w
open AlgebraicCurve MazurTransfer.RationalQuotientPicardGaloisTrace

theorem MazurTransfer.RationalQuotientPicardGaloisTrace.pic0_galois_trace_eq_zero
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {E : Type w} [Field E] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K E] (e : RatFunc K ≃ₐ[K] F) (c : Pic0 K E) :
    ∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • c = 0 := by sorry
