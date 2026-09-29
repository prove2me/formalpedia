-- Prove2me | Theorems.Thm_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
-- name    : ModularCurve.hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/eaeff181-85eb-5efa-addc-5102c2589c8b
-- title:
--   Frobenius push-forward preserves ss-polar differentials and residues
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be of finite index with $T\in\Gamma$, and write $F=$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101), the subfield of $K((q))$ generated over $K$ by the ratios of integral $q$-expansions of modular forms for $\Gamma$. Let $C:\Omega_{F/K}\to\Omega_{F/K}$ be a $K$-linear map which is a Frobenius push-forward on $q$-expansions, i.e. for every $\omega$ the Laurent series `diffQExp` of $C\omega$ is the $p$-decimation `qDecimate K p` of that of $\omega$. Let $\omega\in\Omega_{F/K}$ lie in `ssPolarDifferentials K Γ p`: for every place $v$ of $F/K$ (a valuation subring containing $K$, proper, with principal ideals), $\omega$ is regular at $v$ when $v$ does not satisfy `IsSSPlaceQExp K Γ p`, and has at most a simple pole at $v$ when it does. The conclusion is twofold: $C\omega$ again lies in `ssPolarDifferentials K Γ p`; and for every place $v$ satisfying `IsSSPlaceQExp K Γ p` and every $r\in K$, if $\omega=f\cdot d\pi_v$ with $\pi_v f$ of residue $r$ at $v$, then $C\omega$ has the same simple residue $r$ at the place `qExpFrobeniusPlaceModL K Γ p v`, the restriction of $v$ along the $p$-power $q$-expansion endomorphism of $F$.
--
--   This is the compatibility of the Cartier-type operator on differentials of the characteristic-$p$ $q$-expansion function field with the supersingular polar locus and with residues, the residue being preserved exactly (not raised to the $p$-th power) because the $K$-linear operator factors as the semilinear Cartier operator followed by a Frobenius twist. It feeds the construction of residue data on supersingular-polar differentials used in the level-lowering argument, being cited by [`ModularCurve.mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff`](thm.html#ModularCurve.mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff) and by a criterion for cusp forms to lie in the two-component regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (C : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hC : ModularCurve.IsFrobPushDiff K Γ p C)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) (hω : ω ∈ ModularCurve.ssPolarDifferentials K Γ p) :
    C ω ∈ ModularCurve.ssPolarDifferentials K Γ p ∧
      ∀ v ∈ ModularCurve.ssPlacesQExp K Γ p, ∀ r : K,
        AlgebraicCurve.Place.HasSimpleResidue v ω r →
          AlgebraicCurve.Place.HasSimpleResidue (ModularCurve.qExpFrobeniusPlaceModL K Γ p v) (C ω) r := by sorry
