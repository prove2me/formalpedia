-- Prove2me | Theorems.Thm_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
-- name    : ModularCurve.inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/47537274-653c-54b6-8a76-e72be2065410
-- title:
--   Vanishing of dlog(e_K g) versus triviality of [E]
-- statement:
--   Fix a prime $p$ and $M\ge 1$ with $p\mid M$, a subgroup $H\le(\mathbf Z/M)^\times$, an algebraically closed field $\kappa$ of characteristic $p$, and an algebraically closed field $K$ that is a $\kappa$-algebra. Write $\bar F_\kappa$ for [`ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ`](def/ModularCurve_JHNeronObjectAtP.html#L29), the intermediate field of $\kappa((q))$ obtained by adjoining to $\kappa$ the integral form ratios for the level group `ΓN p M H hpM`, and $\bar F_K$ for [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))`](def/ModularCurve_X1.html#L101), the corresponding subfield of $K((q))$ for the group $\Gamma_{H'}(M/p)\le \mathrm{SL}_2(\mathbf Z)$, where $H'$ is the image of $H$ under $(\mathbf Z/M)^\times\to(\mathbf Z/(M/p))^\times$ and $\Gamma_{H'}(M/p)$ is the image in $\mathrm{SL}_2(\mathbf Z)$ of the preimage of $H'$ under the upper-left-entry character of $\Gamma_0(M/p)$. Given a ring homomorphism $e_K\colon\bar F_\kappa\to\bar F_K$ which on $q$-expansions is the coefficientwise application of $\kappa\to K$, a map $\mathrm{pl}_K$ from places of $\bar F_\kappa/\kappa$ to places of $\bar F_K/K$ (a place being a proper valuation subring containing the constants which is a principal ideal ring) with $\mathrm{ord}_{\mathrm{pl}_K(v)}(e_Kg)=\mathrm{ord}_v(g)$ for all $g$ and $v$, a non-zero $g\in\bar F_\kappa$, and a degree-zero divisor $E$ of $\bar F_\kappa/\kappa$ with $p\,E(v)=\mathrm{ord}_v(g)$ at every place $v$, the conclusion is the equivalence $(e_Kg)^{-1}\cdot d(e_Kg)=0$ in $\Omega_{\bar F_K/K}$ if and only if the class of $E$ in $\mathrm{Pic}^0(\bar F_\kappa/\kappa)=\{\text{degree-zero divisors}\}/\{\text{principal divisors}\}$ vanishes.
--
--   This is the comparison, for the $q$-expansion function fields attached to $\Gamma_H$-level structures in characteristic $p$, between vanishing of the logarithmic differential of a function after extension of the constant field and triviality of the associated $p$-division divisor class, in the style of Serre's description of $\mathrm{Pic}[p]$ by $\mathrm{dlog}$. It feeds the analysis of reduced root functions used in the study of $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra κ K]
    (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (heK : ∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ, ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (g : LaurentSeries κ))
    (plK : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hplK : ∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) (v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)), (plK v).ord (eK g) = v.ord g)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) (hg : g ≠ 0)
    (E : AlgebraicCurve.Divisor.degZero (K := κ) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ))
    (hE : ∀ v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ), (p : ℤ) * (E : AlgebraicCurve.Divisor κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)) v = v.ord g) :
    (eK g)⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (eK g) = 0 ↔ AlgebraicCurve.Pic0.mk E = 0 := by sorry
