-- Prove2me | Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
-- name    : ModularForm.finiteDimensional_of_isArithmetic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/fec292ab-0757-5b48-a9bc-a13e34bc1b49
-- title:
--   Finite-dimensionality of M_k(G) for arithmetic G
-- statement:
--   Let $\mathcal{G}$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ which is arithmetic, i.e. carries the instance `Subgroup.IsArithmetic` expressing commensurability with the image of $\mathrm{SL}_2(\mathbb{Z})$, and all of whose elements have determinant $1$ (the instance `Subgroup.HasDetOne`, which is what gives the space of forms its $\mathbb{C}$-module structure), and let $k$ be an arbitrary integer weight, positive, zero or negative. Then the complex vector space `ModularForm 𝒢 k` of weight-$k$ modular forms for $\mathcal{G}$ — holomorphic functions on the upper half-plane satisfying the weight-$k$ slash-invariance under $\mathcal{G}$ together with the growth condition at the cusps imposed by Mathlib's definition — is finite-dimensional over $\mathbb{C}$. No congruence, torsion-freeness or sign condition on $\mathcal{G}$ is assumed, and no bound on the dimension is asserted: the conclusion is finiteness alone, in the form of the `FiniteDimensional ℂ` instance.
--
--   This is the classical finite-dimensionality of spaces of modular forms of fixed weight on an arithmetic group, here in the uniform form covering all finite-index subgroups of $\mathrm{SL}_2(\mathbb{Z})$, in particular $\Gamma_0(N)$, $\Gamma_1(N)$ and $\Gamma(N)$. It underlies the corresponding statements for cusp forms ([`CuspForm.finiteDimensional_of_isArithmetic`](thm.html#CuspForm.finiteDimensional_of_isArithmetic), [`CuspForm.finiteDimensional_Gamma1`](thm.html#CuspForm.finiteDimensional_Gamma1)) and the construction of bases with controlled $q$-expansion coefficients, and hence the treatment of Hecke operators as a commuting family of endomorphisms of a finite-dimensional space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_finiteDimensional_of_isArithmetic.lean

import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒢 k) := by sorry
