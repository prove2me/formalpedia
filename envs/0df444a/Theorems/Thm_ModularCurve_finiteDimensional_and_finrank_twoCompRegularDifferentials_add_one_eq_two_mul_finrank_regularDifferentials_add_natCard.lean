-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard
-- name    : ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/53e75f3d-01e5-5608-b9c1-6133b0e3cbc9
-- title:
--   Dimension count for two-component supersingular glued differentials
-- statement:
--   Let $K$ be an algebraically closed field, $p$ a prime with $K$ of characteristic $p$, and $\Gamma$ a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix $\mathrm{ModularGroup.T}$; write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ attached to integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ of modular forms $f,g$ of a common weight for $\Gamma$, with $\mathrm{intSeriesC}\,p_g\neq 0$. Assume the set of supersingular places of $F$ over $K$ is non-empty, a place being supersingular when some $x\in F$ whose Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) has a value $a$ at it lying in $\mathrm{ssJSet}\,p\,K$. The conclusion is twofold: first, the submodule [`ModularCurve.twoCompRegularDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L320) of $\Omega[F/K]\times\Omega[F/K]$, namely the $K$-span of the pairs satisfying `IsGluedPolarPair` for the set of node pairs $(\mathrm{Frob}_p(w),w)$ with $w$ supersingular (where $\mathrm{Frob}_p$ is [`ModularCurve.qExpFrobeniusPlaceModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L132)), is finite-dimensional over $K$; second, its $K$-dimension plus $1$ equals twice $\dim_K$ of the regular differentials of $F$ over $K$ — those $\omega\in\Omega[F/K]$ which at every place $v$ can be written $f\cdot v.\mathrm{dCoord}$ with $f$ in the valuation subring of $v$ — plus the number of those node pairs.
--
--   This is the Rosenlicht-style dimension count for the differentials of the two-component curve obtained by glueing two copies of $X(\Gamma)$ along the supersingular points by the Frobenius correspondence, expressed through $\dim_K$ of the regular differentials rather than the genus. It feeds [`ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one`](thm.html#ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one), the dimension input for the mod $p$ differentials of the glued modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hss : (ModularCurve.ssPlacesQExp K Γ p).Nonempty) :
    FiniteDimensional K ↥(ModularCurve.twoCompRegularDifferentials K Γ p) ∧
      Module.finrank K ↥(ModularCurve.twoCompRegularDifferentials K Γ p) + 1 =
        2 * Module.finrank K ↥(AlgebraicCurve.regularDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ)) +
          Nat.card ↥(ModularCurve.ssNodePairsQExp K Γ p) := by sorry
