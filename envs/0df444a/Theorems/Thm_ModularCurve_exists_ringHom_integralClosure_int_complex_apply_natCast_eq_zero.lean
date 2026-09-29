-- Prove2me | Theorems.Thm_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero
-- name    : ModularCurve.exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/786d2c21-6da4-5c7b-81f7-1b1a7a369a5f
-- title:
--   Reduction of ℤ̄ to a characteristic-p algebraically closed field
-- statement:
--   Let $K$ be a field that is algebraically closed, let $p$ be a natural number that is prime, and suppose $K$ has characteristic $p$. Let $\overline{\mathbb Z} =$ `integralClosure ℤ ℂ` denote the subring of $\mathbb C$ consisting of the elements integral over $\mathbb Z$, i.e. the ring of algebraic integers, regarded as a ring in its own right. The assertion is that there exists a ring homomorphism $\varphi \colon \overline{\mathbb Z} \to K$ such that $\varphi$ sends the image of the natural number $p$ in $\overline{\mathbb Z}$ to $0$. No compatibility beyond being a ring homomorphism is imposed, and no uniqueness is claimed: the statement is purely an existence statement for one reduction map killing $p$.
--
--   This is the standard existence of a reduction map from the algebraic integers onto an algebraically closed field of characteristic $p$, obtained by choosing a maximal ideal above $(p)$ and embedding the residue field. It supplies the ambient specialisation homomorphism used when complex-analytically defined quantities (Hecke eigenvalues and coefficients with values in $\overline{\mathbb Z}$) are read in characteristic $p$, and it is invoked by the statements on Hecke correspondences modulo $\mathfrak l$ and on polar differentials with twisted transposed Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ φ : ↥(integralClosure ℤ ℂ) →+* K, φ (p : ↥(integralClosure ℤ ℂ)) = 0 := by sorry
