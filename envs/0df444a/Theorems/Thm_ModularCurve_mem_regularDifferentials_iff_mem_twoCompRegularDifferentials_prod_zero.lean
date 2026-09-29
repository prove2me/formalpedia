-- Prove2me | Theorems.Thm_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero
-- name    : ModularCurve.mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/512c8648-f453-5421-89b0-fb8677681742
-- title:
--   Regularity of ω₁ versus (ω₁,0) being glued-regular
-- statement:
--   Let $K$ be an algebraically closed field, $p$ a prime with $K$ of characteristic $p$, and $\Gamma$ a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$ containing the translation matrix `ModularGroup.T`. Write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the reductions to $K$ of quotients $p_f/p_g$ of integral $q$-expansions of modular forms of some weight for $\Gamma$ (with $p_g$ reducing to a nonzero series). Let $\omega_1 \in \Omega_{F/K}$ be a differential lying in [`ModularCurve.ssPolarDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L35), that is: at every place $v$ of $F/K$ (a valuation subring containing $K$, proper, and a principal ideal ring) which does not satisfy the supersingularity predicate [`ModularCurve.IsSSPlaceQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L23), $\omega_1$ is regular, and at every place which does satisfy it, $\omega_1$ has at most a simple pole. The assertion is an equivalence: $\omega_1$ is everywhere regular, i.e. for each place $v$ there is $f$ in the valuation subring of $v$ with $\omega_1 = f\cdot\, d(\text{uniformizer of } v)$, if and only if the pair $(\omega_1, 0)$ lies in [`ModularCurve.twoCompRegularDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L320), the $K$-span of the pairs satisfying [`AlgebraicCurve.IsGluedPolarPair`](def/AlgebraicCurve_PolarDifferentials.html#L138) for the set of pairs of places $(\,\mathrm{Frob}(v), v\,)$ with $v$ supersingular and $\mathrm{Frob}$ given by [`ModularCurve.qExpFrobeniusPlaceModL`](def/ModularCurve_QExpFrobeniusModL.html#L132).
--
--   This identifies, on the component through the cusps, the regular differentials of the mod-$p$ modular function field with those differentials of the two-component special fibre (two copies of the curve glued along the supersingular points, in the sense of Rosenlicht) whose second component vanishes. It is used in the regularity clause accompanying the Atkin–Lehner comparison of differentials, via [`ModularCurve.coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong`](thm.html#ModularCurve.coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (ω₁ : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hω₁ : ω₁ ∈ ModularCurve.ssPolarDifferentials K Γ p) :
    ω₁ ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K Γ) ↔
      (ω₁, (0 : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])) ∈ ModularCurve.twoCompRegularDifferentials K Γ p := by sorry
