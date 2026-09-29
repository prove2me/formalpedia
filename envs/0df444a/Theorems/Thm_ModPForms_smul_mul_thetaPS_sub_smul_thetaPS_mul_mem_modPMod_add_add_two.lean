-- Prove2me | Theorems.Thm_ModPForms_smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two
-- name    : ModPForms.smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/1fcd2f1e-d78f-59ed-a112-63e804a634cb
-- title:
--   First Rankin–Cohen bracket on mod-p spans of integral forms
-- statement:
--   Let $N' \ge 1$ be a natural number (assumed nonzero), let $k, l \in \mathbb{Z}$, and let $F$ be a field. For a natural number $N$ and a weight $k$, the $F$-submodule $\mathrm{modPMod}\,N\,k\,F$ of $F[[q]]$ is defined as the $F$-span of those power series of the form $\sum_n (a_n \bmod F)\,q^n$, with $a : \mathbb{N} \to \mathbb{Z}$, for which there is a modular form $f$ of weight $k$ on $\Gamma_0(N)$ whose $q$-expansion coefficients (the coefficients of `qExpansion 1 f`, with respect to the period $1$) satisfy $\mathrm{qCoeff}\,f\,n = a_n$ in $\mathbb{C}$ for all $n$; the coefficientwise operator $\mathrm{thetaPS}$ on $F[[q]]$ sends $\varphi$ to the series with $n$-th coefficient $n \cdot (\text{$n$-th coefficient of } \varphi)$, i.e. $\theta = q\,d/dq$ read in $F$. Given $\varphi \in \mathrm{modPMod}\,N'\,k\,F$ and $\psi \in \mathrm{modPMod}\,N'\,l\,F$, the assertion is that $$(k)_F \cdot \bigl(\varphi \cdot \theta\psi\bigr) \; - \; (l)_F \cdot \bigl(\theta\varphi \cdot \psi\bigr) \;\in\; \mathrm{modPMod}\,N'\,(k+l+2)\,F,$$ where $(k)_F, (l)_F$ denote the images of $k, l$ under $\mathbb{Z} \to F$ and the products are multiplication of power series, scalar multiplication being that of the $F$-module $F[[q]]$.
--
--   This transports the first Rankin–Cohen bracket $[f,h]_1 = k\,f\,\theta h - l\,(\theta f)\,h$, of weight $k+l+2$, from modular forms on $\Gamma_0(N')$ to the $F$-spans of coefficientwise reductions of their integral $q$-expansions, in arbitrary characteristic. It is used in the study of the $\theta$-operator on such spans, in particular by [`ModPForms.thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModPForms

theorem ModPForms.smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two
    (N' : ℕ) [NeZero N'] (k l : ℤ) (F : Type) [Field F]
    (φ ψ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) (hψ : ψ ∈ modPMod N' l F) :
    (k : F) • (φ * thetaPS ψ) - (l : F) • (thetaPS φ * ψ) ∈ modPMod N' (k + l + 2) F := by sorry
