-- Prove2me | Theorems.Thm_ModPForms_mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn
-- name    : ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/4fb4f4f9-29f3-5afc-aaca-731070a8e0ee
-- title:
--   Cuspidality of a mod-p form detected by its weight-2m function
-- statement:
--   Let $p\ge 5$ be a prime, let $N\ge 1$ be an integer not divisible by $p$, let $K$ be a field of characteristic $p$ and let $m$ be a natural number. Let $\varphi$ be a power series over $K$ lying in [`ModPForms.modPMod N (2 * (m : ℤ)) K`](def/CuspForm_ModPForms.html#L12), that is, in the $K$-span of those power series arising as the coefficientwise reduction to $K$ of an integral sequence $(a_n)$ which is the $q$-expansion of a weight-$2m$ modular form on $\Gamma_0(N)$. Let $G$ be an element of the intermediate field `modularFunctionFieldC K N` of `LaurentSeries K` generated over $K$ by `jqModC K` and `jqNModC K N`, and assume that $G$, viewed as a Laurent series, satisfies `IsModPCuspFormFn K m`: writing $j$ for `jqModC K`, the element $G^6 j^{4m}(j-1728)^{3m}$ is integral over $K[j]$, and for some natural number $M$ the element $G^{2M} j^{mM+1}(j-1728)^{mM}$ is integral over $K[j^{-1}]$. Assume finally that $G\cdot(\theta_j)^m$, where $\theta_j$ is `thetaJ K`, equals the Laurent series attached to $\varphi$. Then $\varphi$ lies in [`ModPForms.modPCusp N (2 * (m : ℤ)) K`](def/CuspForm_ModPForms.html#L7), the $K$-span of reductions of integral $q$-expansions of weight-$2m$ cusp forms on $\Gamma_0(N)$.
--
--   This is the converse to the passage from a reduction of integral cusp forms to a cuspidal function on the mod-$p$ modular curve: it says that membership in the span of reductions of cusp forms is detected by the integrality conditions on the associated weight-$2m$ function, the argument comparing the dimension of a Riemann–Roch space with the classical dimension formula for $S_{2m}(\Gamma_0(N))$. It is used to produce, for a function satisfying the cuspidal integrality conditions, a cusp-form reduction with the prescribed $q$-expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] (m : ℕ)
    (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K)
    (G : ↥(modularFunctionFieldC K N)) (hG : IsModPCuspFormFn K m (G : LaurentSeries K))
    (hGφ : qexpOfWeight K (m : ℤ) (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ) :
    φ ∈ ModPForms.modPCusp N (2 * (m : ℤ)) K := by sorry
