-- Prove2me | Theorems.Thm_Grothendieck_ae_mulVecE_ne_zero
-- name    : Grothendieck.ae_mulVecE_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:37:18.429498+00:00
-- url     : https://prove2.me/theorems/da8a7e7e-8eb0-442c-88e7-c5ae49453d2b
-- title:
--   A Gaussian column does not vanish: $Zu\neq 0$ almost surely
-- statement:
--   Let $Z$ be a random $r\times n$ matrix with independent standard Gaussian entries, $r\ge 1$, and let $u\in\mathbb{R}^n$ be a nonzero vector. Then $Zu\neq 0$ almost surely.
--
--   The $i$-th coordinate of $Zu$ is the linear form $\ell_u(z)=\sum_j z_j u_j$ applied to the $i$-th row of $Z$. The rows of $Z$ are independent, each distributed as $n$ independent standard Gaussians; the pushforward of that law under $\ell_u$ is the centred Gaussian of variance $\|u\|^2\neq 0$, which has no atoms, so $\ell_u$ vanishes on a null set. Since $r\ge 1$ the matrix has a $0$-th row, and `Measure.pi_eval_preimage_null` transfers the statement from the row law to the product law on $r\times n$ matrices.
--
--   This is the measure-theoretic fact behind the degenerate case $|\langle u,v\rangle|=1$ of the matrix Grothendieck identity of Briët–de Oliveira Filho–Vallentin (Lemma 2.1), and it is what makes the rank-three Gaussian rounding $r_i = GU_i/\|GU_i\|$ well defined almost surely in the Quantum Max Cut rounding argument: the normalisation $\|x\|^{-1}x$ has to be applied to a nonzero vector, and any finite family of columns is simultaneously nonzero almost surely.
--
--   **Formalization note.** The statement is about `mulVecE r n Z u`, the matrix–vector product in the coordinates of `EuclideanSpace`; the proof uses only the law of a single row and the product structure of `gaussianMatrix`.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1, p. 84, the degenerate case |<u,v>| = 1; the almost-sure nonvanishing of a nondegenerate Gaussian image that underlies it.

import Mathlib
import Definitions.Def_Grothendieck_Gaussian

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **A Gaussian column does not vanish.** For a standard Gaussian `r × n` matrix `Z` with
`r ≥ 1` and any nonzero `u`, the column `Zu` is nonzero almost surely: its `0`-th coordinate is
the linear form `z ↦ ∑ i, z i * u.ofLp i` applied to the `0`-th row of `Z`, whose law is
`gaussianReal 0 ‖u‖²` and hence non-atomic. -/
theorem ae_mulVecE_ne_zero {r n : ℕ} (hr : 1 ≤ r) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) : ∀ᵐ Z ∂(gaussianMatrix r n), mulVecE r n Z u ≠ 0 := by sorry

end Grothendieck
