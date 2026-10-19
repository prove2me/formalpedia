-- Prove2me | Theorems.Thm_MazurTransfer_FiniteNondegeneratePairingAdjointKernels_natCard_adjoint_kernels_eq_of_nondegenerate
-- name    : MazurTransfer.FiniteNondegeneratePairingAdjointKernels.natCard_adjoint_kernels_eq_of_nondegenerate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T12:17:00.136546+00:00
-- url     : https://prove2.me/theorems/6216f748-2d01-4c9d-ac79-01ff38a76100
-- title:
--   Equal kernel cardinalities for adjoints of a finite nondegenerate pairing
-- statement:
--   For a finite abelian group P and a field K, a bilinear pairing P × P → Kˣ nondegenerate in both variables makes any two adjoint additive endomorphisms have equal kernel cardinalities. Character surjectivity is proved from nondegeneracy and finite character counting and is not an additional premise.
-- source:
--   MazurTheorem FiniteNondegeneratePairingAdjointKernels.natCard_adjoint_kernels_eq_of_nondegenerate; finite-character arguments reuse official Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2 under Apache-2.0.

import Mathlib
noncomputable section

theorem MazurTransfer.FiniteNondegeneratePairingAdjointKernels.natCard_adjoint_kernels_eq_of_nondegenerate {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0)
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card T.ker = Nat.card T'.ker := by sorry
