-- Prove2me | Theorems.Thm_MazurTransfer_original_finite_free_hopf_arithmetic_point_rank
-- name    : MazurTransfer.original_finite_free_hopf_arithmetic_point_rank
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T19:03:05.390161+00:00
-- url     : https://prove2.me/theorems/905c16a6-b252-431f-a291-66fff6246ee2
-- statement:
--   The rank of the original finite-free Hopf algebra equals the cardinality of its given arithmetic point labels over the same algebraically closed characteristic-zero field. The complete original proposition and helper type, with every coefficient ring, Hopf structure, finiteness, freeness, field, algebra and universe hypothesis, are independently checked. Named downstream consumer: cyclotomic classification of the same selected integral character quotient.

import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
noncomputable section
universe u v w x

theorem MazurTransfer.original_finite_free_hopf_arithmetic_point_rank : ∀ {R : Type u} [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] (K : Type w) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] {M : Type x} (e : WithConv (H →ₐ[R] K) ≃ M), Module.finrank R H = Nat.card M := by sorry
