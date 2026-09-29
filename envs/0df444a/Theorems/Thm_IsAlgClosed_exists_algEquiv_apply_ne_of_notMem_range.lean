-- Prove2me | Theorems.Thm_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range
-- name    : IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/fbab5d1c-288a-574d-bde8-52352ebf6d8e
-- title:
--   Elements outside F are moved by some F-automorphism of E
-- statement:
--   Let $F$ and $E$ be fields, with $E$ an $F$-algebra, $E$ algebraically closed, and $F$ of characteristic zero. Let $c$ be an element of $E$ that does not lie in the image of the structure map $\mathrm{algebraMap}\ F\ E$, i.e. $c \notin \mathrm{Set.range}\ (\mathrm{algebraMap}\ F\ E)$. Then there exists an $F$-algebra automorphism $\sigma : E \simeq_{\mathrm{alg}[F]} E$ of $E$ with $\sigma(c) \neq c$. Equivalently: the fixed field of the group of $F$-algebra automorphisms of $E$ is exactly the image of $F$ in $E$, the inclusion of that image in the fixed field being trivial. No separability, finiteness or algebraicity assumption is imposed on the extension $E/F$; $c$ may be algebraic or transcendental over $F$, and both standing hypotheses on $E$ (algebraically closed) and on $F$ (characteristic zero) are genuinely used.
--
--   This is the standard fixed-field statement for the automorphism group of an algebraically closed extension in characteristic zero. It serves as the Galois-descent input for the $q$-expansion arguments on modular and cusp forms, being cited by [`ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp`](thm.html#ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp), [`CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp`](thm.html#CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp) and [`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`](thm.html#CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top), where a form whose coefficients are fixed by every automorphism of $\mathbb{C}$ over a cyclotomic field is shown to have coefficients in that field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E} (hc : c ∉ Set.range (algebraMap F E)) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by sorry
