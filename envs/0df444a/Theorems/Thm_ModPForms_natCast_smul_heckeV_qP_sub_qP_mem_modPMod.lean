-- Prove2me | Theorems.Thm_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
-- name    : ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/5f14fc28-3cf7-5048-80bb-b6f50e5f89b7
-- title:
--   Reduction of ℓ E₂(ℓτ)-E₂(τ) lies in mod-p weight-2 forms
-- statement:
--   Let $\ell$ be a prime and $F$ a field. Write $\widetilde P =$ [`SwdAlgebra.qP F`](def/SwdAlgebra.html#L11) for the power series over $F$ obtained by applying the ring homomorphism $\mathbb{Z} \to F$ to the integral series whose $n$-th coefficient is $1$ for $n = 0$ and $-24\sum_{d \mid n} d$ for $n \neq 0$, and let [`PowerSeries.heckeV ℓ`](def/PowerSeries_FormalHeckeOperators.html#L20) be the $F$-linear operator on $F\llbracket X\rrbracket$ sending $f$ to the series whose $n$-th coefficient is the $(n/\ell)$-th coefficient of $f$ when $\ell \mid n$ and $0$ otherwise, i.e. the substitution $q \mapsto q^{\ell}$. The assertion is that $(\ell : F) \cdot \mathrm{heckeV}_\ell(\widetilde P) - \widetilde P$ belongs to the submodule [`ModPForms.modPMod ℓ 2 F`](def/CuspForm_ModPForms.html#L12) of $F\llbracket X\rrbracket$, that is, to the $F$-span of those power series of the form $\sum_n \overline{a(n)} X^n$ with $a : \mathbb{N} \to \mathbb{Z}$ for which there exists a modular form $f$ of weight $2$ on $\Gamma_0(\ell)$ whose $q$-expansion coefficients (the coefficients of `qExpansion 1 f`) satisfy $\mathrm{qCoeff}(f)(n) = a(n)$ in $\mathbb{C}$ for all $n$, the reduction being taken coefficientwise along $\mathbb{Z} \to F$.
--
--   The element $\ell\,\widetilde P(q^{\ell}) - \widetilde P(q)$ is the reduction of the weight-$2$ Eisenstein series $\ell E_2(\ell\tau) - E_2(\tau)$ on $\Gamma_0(\ell)$, with $q$-expansion $(\ell-1) + 24\sum_{n\ge 1}\sigma'_\ell(n)q^n$ where $\sigma'_\ell(n) = \sum_{d \mid n,\ \ell \nmid d} d$; it is the modular input needed to see that certain explicit power series lie in the mod-$p$ forms of the relevant weight and level. It is used in the results on membership of the theta series [`ModPForms.thetaPS`](def/CuspForm_ModPForms.html#L17) in [`ModPForms.modPMod`](def/CuspForm_ModPForms.html#L12) of weight $k+2$ and $k+4$, and in [`ModularCurve.exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd`](thm.html#ModularCurve.exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_SwdAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] :
    (ℓ : F) • PowerSeries.heckeV ℓ (SwdAlgebra.qP F) - SwdAlgebra.qP F ∈ ModPForms.modPMod ℓ 2 F := by sorry
