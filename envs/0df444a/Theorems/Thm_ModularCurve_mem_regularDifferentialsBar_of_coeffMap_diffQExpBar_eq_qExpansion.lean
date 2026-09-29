-- Prove2me | Theorems.Thm_ModularCurve_mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion
-- name    : ModularCurve.mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/3de790c0-e31d-557a-923c-f1bd5c76694c
-- title:
--   Weight-2 cusp form q-expansion forces a regular differential
-- statement:
--   Let $N$ be a nonzero natural number, let $\iota_0 : \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism from `AlgebraicClosure ℚ` to $\mathbb{C}$, let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$, and let $\omega$ be a Kähler differential of the field $\bar F_N =$ `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$; here $\bar F_N$ is the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image, under the coefficientwise embedding $\mathbb{Q}((q)) \to \overline{\mathbb{Q}}((q))$, of `modularFunctionFieldFull N`, itself the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions `divisorExpansions N`. Assume that the Laurent series $\mathrm{diffQExpBar}_N(\omega) \in \overline{\mathbb{Q}}((q))$, obtained by applying to $\omega$ the $\bar F_N$-linear map `diffQExp` that lifts the derivation `qEulerOn` of $\bar F_N$, becomes, after applying $\iota_0$ to all coefficients, exactly the image in $\mathbb{C}((q))$ of the power series `UpperHalfPlane.qExpansion 1 f`. Then $\omega$ lies in `regularDifferentialsBar N`, that is, in `regularDifferentials` of $\bar F_N$ over $\overline{\mathbb{Q}}$: for every place $v$ of $\bar F_N$ over $\overline{\mathbb{Q}}$ there is an element $g$ of the valuation subring of $v$ with $\omega = g \cdot v.\mathrm{dCoord}$.
--
--   This is the arithmetic form of the classical statement that $\omega = 2\pi i f(z)\,dz = f(q)\,dq/q$ is a holomorphic differential on $X_0(N)$ when $f$ is a weight-2 cusp form, phrased for the algebraic model $\bar F_N/\overline{\mathbb{Q}}$ of the modular curve and its places. It is the regularity half of the identification of $S_2(\Gamma_0(N))$ with the space of regular differentials, used in [`ModularCurve.exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm`](thm.html#ModularCurve.exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm) and in the construction of integral regular differentials with prescribed $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion (N : ℕ)
    [NeZero N] (ι₀ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hω : ModularCurve.coeffMap ι₀ (ModularCurve.diffQExpBar N ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f)) :
    ω ∈ ModularCurve.regularDifferentialsBar N := by sorry
