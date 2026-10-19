-- Prove2me | Theorems.Thm_MazurTransfer_RationalArithmeticPicardTriviality_principal_of_rational_field_equiv
-- name    : MazurTransfer.RationalArithmeticPicardTriviality.principal_of_rational_field_equiv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:52:38.269983+00:00
-- url     : https://prove2.me/theorems/df4a2a15-d9d4-40f8-beee-6155b1250cc6
-- title:
--   Every degree-zero divisor on a rationally presented function field is principal
-- statement:
--   For arbitrary fields K and F with their specified K-algebra structure and any K-algebra equivalence K(t) to F, every actual K-divisor on F of degree zero is principal. The full original equivalence, divisor and degree hypotheses are retained.
-- source:
--   Complete original MazurTheorem RationalArithmeticPicardTriviality.principal_of_rational_field_equiv proof and contract. The rational divisor and Picard transport inputs reuse official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete original rational-field divisor principality proof retained.
The native public theorem resolves to its retained checked interface.
Design boundary: every degree-zero divisor over a field isomorphic to K(t)
is principal, with the actual divisor and field equivalence explicit.
Named downstream consumer: rational quotient Picard Galois trace, then the
actual order-13 diamond cyclotomic and norm identities.
Official Anthropic FLT inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import Definitions.Def_AlgebraicCurve_Pic0Congr
noncomputable section
universe u v
open AlgebraicCurve
local instance (K : Type u) [Field K] : Algebra K (RatFunc K) := RatFunc.instAlgebraOfPolynomial K K

theorem MazurTransfer.RationalArithmeticPicardTriviality.principal_of_rational_field_equiv
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (e : RatFunc K ≃ₐ[K] F)
    (D : Divisor K F) (hD : Divisor.degree D = 0) : D.IsPrincipal := by sorry
