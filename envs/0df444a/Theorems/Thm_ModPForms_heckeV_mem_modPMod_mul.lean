-- Prove2me | Theorems.Thm_ModPForms_heckeV_mem_modPMod_mul
-- name    : ModPForms.heckeV_mem_modPMod_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/c28d7488-9d49-5c68-a0af-0f6107052278
-- title:
--   V_ℓ maps mod-p forms of level N to level Nℓ
-- statement:
--   Let $N$ be a nonzero natural number, $k$ an integer, $\ell$ a nonzero natural number and $F$ a field. Write $\widetilde M_k(\Gamma_0(N);F)$ for the $F$-submodule [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12) of $F[\![X]\!]$, defined as the $F$-span of those power series $\varphi$ for which there is a modular form $f$ of weight $k$ on $\Gamma_0(N)$ and a sequence $a\colon\mathbb N\to\mathbb Z$ with $\mathrm{qCoeff}(f,n)=a_n$ in $\mathbb C$ for every $n$ (the $n$-th coefficient of the width-one $q$-expansion of $f$) and $\varphi=\sum_n \overline{a_n}\,X^n$, the coefficients being the images of the $a_n$ in $F$. The assertion is: if $\varphi\in\widetilde M_k(\Gamma_0(N);F)$, then $V_\ell\varphi\in\widetilde M_k(\Gamma_0(N\ell);F)$, where $V_\ell=$ [`PowerSeries.heckeV ℓ`](def/PowerSeries_FormalHeckeOperators.html#L20) is the $F$-linear map sending $\varphi$ to the series whose $n$-th coefficient is the $(n/\ell)$-th coefficient of $\varphi$ when $\ell\mid n$ and $0$ otherwise, i.e. the substitution $\varphi(X)\mapsto\varphi(X^\ell)$.
--
--   This is the mod-$p$ shadow of the classical degeneracy (level-raising) map $f(\tau)\mapsto f(\ell\tau)\colon M_k(\Gamma_0(N))\to M_k(\Gamma_0(N\ell))$, which on $q$-expansions is $a_n\mapsto a_{n/\ell}$ and hence preserves integrality. It is used in the construction of mod-$p$ forms of raised level, notably in [`ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two`](thm.html#ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two) and in the analysis of the $j$-expansion at affine geometric places on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_heckeV_mem_modPMod_mul.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.heckeV_mem_modPMod_mul (N : ℕ) [NeZero N] (k : ℤ) (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (F : Type) [Field F] (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F) :
    PowerSeries.heckeV ℓ φ ∈ ModPForms.modPMod (N * ℓ) k F := by sorry
