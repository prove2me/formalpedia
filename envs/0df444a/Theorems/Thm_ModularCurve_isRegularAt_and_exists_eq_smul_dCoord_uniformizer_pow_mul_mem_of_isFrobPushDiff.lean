-- Prove2me | Theorems.Thm_ModularCurve_isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
-- name    : ModularCurve.isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/cce5391f-ed0c-5261-9b75-59f10935967e
-- title:
--   Frobenius push-forward divides supersingular pole orders by p
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$, with $p$ prime, let $\Gamma\le\mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $T$, and write $F=$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by the ratios of integral $q$-expansions of modular forms for $\Gamma$. Let $C$ be a $K$-linear endomorphism of $\Omega_{F/K}$ satisfying [`ModularCurve.IsFrobPushDiff`](def/ModularCurve_XHDifferentialsModL.html#L97), i.e. for every $\omega$ the $q$-expansion `diffQExp` of $C\omega$ is obtained from that of $\omega$ by the decimation $\sum a_m q^m\mapsto\sum a_{pm}q^m$. Let $n\in\mathbb{N}$ and let $\omega\in\Omega_{F/K}$ be such that: at every place $v$ of $F/K$ (a proper valuation subring containing $K$ whose ring is a principal ideal ring) outside the supersingular set `ssPlacesQExp K Γ p` — the places at which the element of $F$ with $q$-expansion $j$ takes a value lying in the supersingular $j$-set for $p$ — one has $\omega=f\cdot v.\mathrm{dCoord}$ for some $f$ in the valuation subring of $v$, where $v.\mathrm{dCoord}=d(\pi_v)$ for a chosen uniformiser $\pi_v$; and at every supersingular place $v$ there is $f\in F$ with $\omega=f\cdot v.\mathrm{dCoord}$ and $\pi_v^{\,n}f$ in the valuation subring of $v$. Then $C\omega$ satisfies the same two conditions with $n$ replaced by the natural-number quotient $(n+p-1)/p$: it is regular at every non-supersingular place, and at every supersingular place $v$ there is $g\in F$ with $C\omega=g\cdot v.\mathrm{dCoord}$ and $\pi_v^{\lceil n/p\rceil}g$ in the valuation subring of $v$.
--
--   This is the statement that the Frobenius push-forward operator on differentials of the modular curve in characteristic $p$ preserves regularity away from the supersingular points and divides the allowed pole order at the supersingular points by $p$ (rounding up); the cases $n=0,1$ say that it preserves regular differentials and differentials with at most simple supersingular poles. It is used in the pole-descent argument for reductions of differentials attached to two-cusp data, via [`CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet`](thm.html#CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (C : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hC : ModularCurve.IsFrobPushDiff K Γ p C)
    (n : ℕ) (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hreg : ∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      v ∉ ModularCurve.ssPlacesQExp K Γ p → v.IsRegularAt ω)
    (hpole : ∀ v ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ f : ↥(ModularCurve.qExpFunctionFieldC K Γ),
      ω = f • v.dCoord ∧ v.uniformizer ^ n * f ∈ v.toValuationSubring) :
    (∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
        v ∉ ModularCurve.ssPlacesQExp K Γ p → v.IsRegularAt (C ω)) ∧
      (∀ v ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ g : ↥(ModularCurve.qExpFunctionFieldC K Γ),
        C ω = g • v.dCoord ∧ v.uniformizer ^ ((n + p - 1) / p) * g ∈ v.toValuationSubring) := by sorry
