-- Prove2me | Theorems.Thm_ModularCurve_moduleFinite_int_heckeAlg_quotient_annihilator_jZero_of_neZero
-- name    : ModularCurve.moduleFinite_int_heckeAlg_quotient_annihilator_jZero_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/8bb23e0f-ec56-5150-8756-29860f356107
-- title:
--   Hecke algebra modulo the annihilator of J₀(M) is ℤ-finite
-- statement:
--   Let $M$ be a natural number with $M \neq 0$. Write `HeckeAlg` for the polynomial ring $\mathbb{Z}[x_\ell : \ell \text{ prime}]$ on indeterminates indexed by the primes, and `JZero M` for $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar M` over $\overline{\mathbb{Q}}$, that is, the group of degree-zero divisors modulo principal divisors for the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $M$. Equip `JZero M` with the `HeckeAlg`-module structure `heckeModuleBar M`: if the operators `heckeOperatorBar M ℓ` ($\ell$ prime) commute pairwise, this is the structure obtained by restriction of scalars along the ring homomorphism `heckeEvalBar` sending the indeterminate at $\ell$ to `heckeOperatorBar M ℓ` in $\mathrm{End}_{\mathbb{Z}}(\mathtt{JZero } M)$, and otherwise the structure obtained by evaluating all indeterminates at $0$. The assertion is that the quotient of `HeckeAlg` by `Module.annihilator HeckeAlg (JZero M)`, the ideal of polynomials annihilating every element of `JZero M`, is a finite (equivalently, finitely generated) $\mathbb{Z}$-module.
--
--   This is the finiteness over $\mathbb{Z}$ of the Hecke algebra acting faithfully on the Jacobian $J_0(M)$, at an arbitrary level $M \neq 0$. It is used to show that a maximal ideal $\mathfrak{m}$ of `HeckeAlg` with non-zero $\mathfrak{m}$-torsion in `JZero M` has finite residue field, which is what the construction of the associated mod-$p$ matrix representation with prescribed traces and determinants of Frobenius elements requires.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduleFinite_int_heckeAlg_quotient_annihilator_jZero_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.moduleFinite_int_heckeAlg_quotient_annihilator_jZero_of_neZero (M : ℕ) [NeZero M] :
    letI := heckeModuleBar M
    Module.Finite ℤ (HeckeAlg ⧸ Module.annihilator HeckeAlg (JZero M)) := by sorry
