-- Prove2me | Theorems.Thm_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot
-- name    : IntermediateField.exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ac579912-a828-5c37-a76c-9f40156c8a26
-- title:
--   Complex embedding sending a primitive q-th root of unity to e^{2π i/q}
-- statement:
--   Let $k_0$ be an intermediate field between $\mathbb{Q}$ and the algebraic closure $\overline{\mathbb{Q}}$ (Mathlib's `AlgebraicClosure ℚ`), let $q$ be a nonzero natural number, and let $\xi$ be an element of $k_0$ which is a primitive $q$-th root of unity, i.e. $\xi^q = 1$ and every natural number $l$ with $\xi^l = 1$ is divisible by $q$. The assertion is that there exists a ring homomorphism $\iota : k_0 \to \mathbb{C}$ with $$\iota(\xi) = \exp\!\left(\frac{2\pi i}{q}\right),$$ the argument being $2 \cdot \pi \cdot i$ divided by the image of $q$ in $\mathbb{C}$. Only a homomorphism of rings is produced in the conclusion, not explicitly a $\mathbb{Q}$-algebra map (the two of course coincide here), and no finiteness or normality hypothesis is placed on $k_0$; the point of the statement is that among the complex embeddings of $k_0$ one may be chosen that reads the prescribed root of unity as the standard exponential, rather than as some other primitive $q$-th root.
--
--   This is the elementary cyclotomic normalisation statement that a chosen primitive $q$-th root of unity in a subfield of $\overline{\mathbb{Q}}$ may be matched with $e^{2\pi i/q}$ by a suitable complex embedding; it supplies the 'complex reading' datum used in the analysis of modular curves of full level, being cited by the two statements [`ModularCurve.FullLevel.exists_supersingularDVR_affineChart_poles_moduliHasse_commonChart_nodes_igusaSep_inertia_of_levelField_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularDVR_affineChart_poles_moduliHasse_commonChart_nodes_igusaSep_inertia_of_levelField_of_eq_three_of_dvd) and `…_of_eq_two_of_dvd`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ) [NeZero q]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := by sorry
