-- Prove2me | Theorems.Thm_ModularCurve_mem_regularDifferentials_of_mem_twoCompRegularDifferentials_of_fst_eq_zero
-- name    : ModularCurve.mem_regularDifferentials_of_mem_twoCompRegularDifferentials_of_fst_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/97c452eb-020f-58e9-a045-b15284583c66
-- title:
--   Glued differentials vanishing on one component are regular
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ for a prime $p$, let $\Gamma\le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $T$, and let $F=$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of $K((q))$ generated over $K$ by the ratios $\overline{p_f}/\overline{p_g}$ of coefficientwise reductions to $K$ of integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ of modular forms $f,g$ of a common weight on $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb{R})$), with $\overline{p_g}\ne 0$. Let $\omega=(\omega_1,\omega_2)$ be a pair of elements of the module $\Omega[F/K]$ of Kähler differentials, and assume that $\omega$ lies in [`ModularCurve.twoCompRegularDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L320), that is, in the $K$-span of the pairs satisfying [`AlgebraicCurve.IsGluedPolarPair`](def/AlgebraicCurve_PolarDifferentials.html#L138) for the set of pairs of places $(v_1,v_2)$ of $F/K$ with $v_2 \in$ [`ModularCurve.ssPlacesQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L27) and $v_1 =$ [`ModularCurve.qExpFrobeniusPlaceModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L132) $v_2$. If $\omega_1=0$, then $\omega_2$ is a regular differential: for every place $v$ of $F/K$ (a valuation subring of $F$, proper, containing the image of $K$ and a principal ideal ring) there is $f$ in that valuation subring with $\omega_2=f\cdot D_{K/F}(\pi_v)$ for the chosen uniformizer $\pi_v$ of $v$.
--
--   This identifies the kernel of the restriction-to-the-first-component map on the differentials of the two-component curve obtained by gluing two copies of $X(\Gamma)_{/K}$ along the supersingular places: a glued pair with vanishing first component has residue zero at each supersingular place, hence no pole there. It feeds the dimension count [`ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard`](thm.html#ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard) for the glued differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_regularDifferentials_of_mem_twoCompRegularDifferentials_of_fst_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.mem_regularDifferentials_of_mem_twoCompRegularDifferentials_of_fst_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] × Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hω : ω ∈ ModularCurve.twoCompRegularDifferentials K Γ p) (h0 : ω.1 = 0) :
    ω.2 ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K Γ) := by sorry
