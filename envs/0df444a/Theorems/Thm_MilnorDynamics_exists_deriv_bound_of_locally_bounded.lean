-- Prove2me | Theorems.Thm_MilnorDynamics_exists_deriv_bound_of_locally_bounded
-- name    : MilnorDynamics.exists_deriv_bound_of_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T23:47:41.108338+00:00
-- url     : https://prove2.me/theorems/ebf36aae-f2f6-4677-8abb-e7c53f4344d9
-- title:
--   Cauchy estimate - a locally bounded holomorphic family has uniformly bounded derivatives on compacta
-- statement:
--   **Cauchy estimates give uniform derivative bounds.** Let $U\subseteq\mathbb C$ be open and let $f_n$ be holomorphic on $U$, with the family locally bounded: on every compact $K\subseteq U$ there is $M$ with $|f_n(z)|\le M$ for all $n$ and all $z\in K$. Then on every compact $K\subseteq U$ the derivatives are uniformly bounded:
--
--   $$\exists B,\quad \forall n,\ \forall z\in K,\quad |f_n'(z)|\le B .$$
--
--   Proof. A compact set strictly inside an open set has positive distance to the complement, so there is $R>0$ with the closed $R$-neighbourhood of $K$ still contained in $U$. Local boundedness applied to that neighbourhood gives a single $M$ valid for all $n$ on a disc of radius $R$ about any point of $K$, and Cauchy's estimate $|f_n'(z)|\le M/R$ then bounds the derivative uniformly.
--
--   This is the equicontinuity input for the Montel/Arzela-Ascoli extraction principle: bounded derivatives on compacta bound the oscillation of the family.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the standard Cauchy estimate for the derivative of a bounded holomorphic function.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_deriv_bound_of_locally_bounded (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∀ K ⊆ U, IsCompact K → ∃ B, ∀ n, ∀ z ∈ K, ‖deriv (f n) z‖ ≤ B := by sorry

end MilnorDynamics
