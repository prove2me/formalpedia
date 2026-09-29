-- Prove2me | Theorems.Thm_ModularCurve_mem_regularDifferentials_of_diffQExp_eq_intSeriesC_of_isIntegralQExp_cuspForm_gammaH_of_not_dvd
-- name    : ModularCurve.mem_regularDifferentials_of_diffQExp_eq_intSeriesC_of_isIntegralQExp_cuspForm_gammaH_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/084dac08-b3fb-5cd6-89a6-432da3ce1cbf
-- title:
--   Regularity of differentials with integral cuspidal q-expansion
-- statement:
--   Let $p$ be a prime and $N \ge 1$ with $p \nmid N$, let $H'$ be a subgroup of $(\mathbb{Z}/N)^{\times}$, and let $K$ be an algebraically closed field of characteristic $p$ (carrying a $\mathbb{Z}/p$-algebra structure). Write $\Gamma =$ [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained as the image in $\mathrm{SL}(2,\mathbb{Z})$ of the preimage, under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^{\times}$ sending a matrix to the reduction of its lower-right entry, of $H'$. Let $g$ be a cusp form of weight $2$ for $\Gamma$ (viewed inside $\mathrm{GL}(2,\mathbb{R})$) and let $p_g \in \mathbb{Z}[[q]]$ satisfy `IsIntegralQExp`, i.e. the image of $p_g$ under $\mathbb{Z} \to \mathbb{C}$ is the $q$-expansion of $g$ at width $1$. Let $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of $K((q))$ generated over $K$ by all quotients $\bar p_f/\bar p_h$ of reductions to $K$ of integral $q$-expansions of modular forms for $\Gamma$ (with nonzero denominator), and let $\omega \in \Omega_{F/K}$ be a Kähler differential whose image under `diffQExp`, the lift to $\Omega_{F/K}$ of the $q$-Euler derivation $F \to K((q))$, equals the Laurent series $\bar p_g$ obtained from $p_g$ by reducing its coefficients into $K$. Then $\omega$ lies in [`AlgebraicCurve.regularDifferentials`](def/AlgebraicCurve_RegularDifferentials.html#L26): for every place $v$ of $F/K$, that is, every proper valuation subring of $F$ containing the image of $K$ and having principal ideals, there is $f$ in that valuation subring with $\omega = f \cdot d(\pi_v)$, where $\pi_v$ is the chosen uniformiser of $v$.
--
--   This is the statement that, for level prime to $p$, a differential on the modular curve attached to $\Gamma_{H'}(N)$ over $K$ whose $q$-expansion is the reduction of an integral weight-$2$ cusp form is everywhere regular — the 'holomorphic reduction of $p$-old forms' input in the $q$-expansion approach to level lowering. It is used in the companion statement on Frobenius-pushed differentials, [`CuspForm.add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC`](thm.html#CuspForm.add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_regularDifferentials_of_diffQExp_eq_intSeriesC_of_isIntegralQExp_cuspForm_gammaH_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.mem_regularDifferentials_of_diffQExp_eq_intSeriesC_of_isIntegralQExp_cuspForm_gammaH_of_not_dvd
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (g : CuspForm (CohCarrier.GammaH N H') 2) (pg : PowerSeries ℤ) (hg : ModularCurve.IsIntegralQExp (⇑g) pg)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K])
    (hω : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ω = ModularCurve.intSeriesC K pg) :
    ω ∈ AlgebraicCurve.regularDifferentials K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) := by sorry
