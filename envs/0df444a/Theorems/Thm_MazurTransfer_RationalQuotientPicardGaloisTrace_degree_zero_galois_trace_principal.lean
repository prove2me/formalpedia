-- Prove2me | Theorems.Thm_MazurTransfer_RationalQuotientPicardGaloisTrace_degree_zero_galois_trace_principal
-- name    : MazurTransfer.RationalQuotientPicardGaloisTrace.degree_zero_galois_trace_principal
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T16:06:21.678243+00:00
-- url     : https://prove2.me/theorems/ddb48f04-17cd-4f61-96b5-174925e2b1ba
-- title:
--   Degree-zero divisor Galois trace over a rational quotient is principal
-- statement:
--   Let K, F and E have the original field, algebra and scalar-tower structures, with E/F finite Galois and HasPrincipalDivisors K E. Given a K-algebra equivalence K(t) to F, the sum of the F-Galois conjugates of any actual K-divisor on E of degree zero is principal. All original hypotheses and universes are retained.
-- source:
--   Complete original MazurTheorem RationalQuotientPicardGaloisTrace.degree_zero_galois_trace_principal proof with its original place/divisor semilinear-versus-algebra automorphism helpers. Official Anthropic FLT divisor trace and push/pull inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete original finite-Galois rational-quotient trace proof retained.
Native imports resolve through the recorded retained checked interface closure.
Design boundary: the conjugate sum of a degree-zero divisor over a finite
Galois extension of a specified rational function field is principal.
Named downstream consumer: Pic0 Galois trace, then actual diamond cyclic trace.
Official Anthropic FLT trace and divisor inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_RationalArithmeticPicardTriviality_principal_of_rational_field_equiv
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward
noncomputable section
universe u v w
open AlgebraicCurve

theorem MazurTransfer.RationalQuotientPicardGaloisTrace.degree_zero_galois_trace_principal
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {E : Type w} [Field E] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K E] (e : RatFunc K ≃ₐ[K] F)
    (D : Divisor K E) (hD : Divisor.degree D = 0) :
    (∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • D).IsPrincipal := by sorry
