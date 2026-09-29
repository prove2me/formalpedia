-- Prove2me | Theorems.Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd
-- name    : ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/42abdcfd-9dd5-5230-957a-5d111427409d
-- title:
--   q-expansion of the Hecke differential operator for ℓ ∣ N
-- statement:
--   Fix a level $N$ (a natural number, nonzero) and a natural number $\ell$ carrying a primality instance, and assume $\ell \mid N$. Let $F_N$ denote `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` obtained as `laurentBaseChange`, i.e. generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull N`, the subfield of $\mathrm{LaurentSeries}(\mathbb{Q})$ generated over $\mathbb{Q}$ by `divisorExpansions N`. Let $\omega$ be an arbitrary element of the module of Kähler differentials $\Omega[F_N \,/\, \overline{\mathbb{Q}}]$, with no regularity hypothesis imposed, and let $n$ be an integer. Write $\Theta =$ `diffQExpBar N` for the $F_N$-linear map $\Omega[F_N/\overline{\mathbb{Q}}] \to \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ obtained by lifting `qEulerOn` through the universal property of the differentials, and $U =$ `heckeDiffBar N ⟨ℓ, Fact.out⟩` for the $\overline{\mathbb{Q}}$-linear endomorphism of $\Omega[F_N/\overline{\mathbb{Q}}]$ given by `Differential.correspondence` applied to the two embeddings `heckeBetaBar` and `heckeAlphaBar` at level $N$ and prime $\ell$. The assertion is the equality of Laurent coefficients $(\Theta(U\omega))_n = (\Theta\omega)_{n\ell}$, the index on the right being the product of $n$ with the integer image of $\ell$.
--
--   This is the $q$-expansion identity expressing that, at a prime $\ell$ dividing the level, the differential Hecke correspondence acts as the Atkin–Lehner operator $U_\ell$, $a_n \mapsto a_{n\ell}$, on expansions $h(q)\,dq/q$ of meromorphic differentials of level $N$; the divisibility hypothesis is what makes the degree of the correspondence $\ell$ rather than $\ell+1$, as recorded by [`ModularCurve.finrankAlong_heckeBetaBar`](thm.html#ModularCurve.finrankAlong_heckeBetaBar). It supplies the bad-prime clause used in transferring relations between Hecke operators on the Jacobian to the Hecke algebra acting on weight-two cusp forms, and is cited by [`ModularCurve.aeval_heckeAlgebra_eq_zero_of_forall_smul_jZero_eq_zero`](thm.html#ModularCurve.aeval_heckeAlgebra_eq_zero_of_forall_smul_jZero_eq_zero), [`ModularCurve.coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen`](thm.html#ModularCurve.coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen) and [`ModularCurve.freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_heckeDiffBar_eq_zero`](thm.html#ModularCurve.freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_heckeDiffBar_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_dvd (N : ℕ) [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExpBar N (ModularCurve.heckeDiffBar N ⟨ℓ, Fact.out⟩ ω)).coeff n =
      (ModularCurve.diffQExpBar N ω).coeff (n * ℓ) := by sorry
