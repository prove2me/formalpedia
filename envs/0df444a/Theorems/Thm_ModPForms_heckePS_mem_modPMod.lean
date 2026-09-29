-- Prove2me | Theorems.Thm_ModPForms_heckePS_mem_modPMod
-- name    : ModPForms.heckePS_mem_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/7fd65d8f-c50b-5c7e-8507-019b635aba03
-- title:
--   Hecke stability of spans of reduced integral q-expansions
-- statement:
--   Let $N' \ge 1$ be a natural number, $F$ a field, $k$ an integer, and $\ell$ a natural number that is prime and does not divide $N'$. Write $\widetilde M$ for [`ModPForms.modPMod N' k F`](def/CuspForm_ModPForms.html#L12), the $F$-submodule of $F[[q]]$ spanned by those power series of the form `PowerSeries.mk fun n => ((a n : ℤ) : F)` for which there exist a modular form $f$ of weight $k$ on $\Gamma_0(N')$ and a function $a : \mathbb{N} \to \mathbb{Z}$ with $\mathrm{qCoeff}(f)(n) = a(n)$ in $\mathbb{C}$ for all $n$, where $\mathrm{qCoeff}(f)(n)$ is the $n$-th coefficient of the $q$-expansion of $f$ taken with period $1$. The assertion is that for every $\varphi \in \widetilde M$ the power series [`ModPForms.heckePS k ℓ φ`](def/CuspForm_ModPForms.html#L20), whose $n$-th coefficient is
--   $$\varphi_{n\ell} + \begin{cases} (\ell : F)^{k-1}\,\varphi_{n/\ell} & \ell \mid n,\\ 0 & \text{otherwise,}\end{cases}$$
--   the power $(\ell:F)^{k-1}$ being an integer power in the field $F$, again lies in $\widetilde M$. Thus $\widetilde M$ is stable under the coefficientwise Hecke operator $T_\ell$ for $\ell \nmid N'$; no hypothesis is imposed on the characteristic of $F$.
--
--   This is the stability of the mod-$p$ space of weight-$k$ forms of level $N'$ under the Hecke operator $T_\ell$ at a prime $\ell$ not dividing the level, formulated purely in terms of $q$-expansions. It supplies the Hecke-stability input used in [`ModPForms.nonempty_ssDatum_algebraicClosure`](thm.html#ModPForms.nonempty_ssDatum_algebraicClosure) and in [`ModPForms.eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two`](thm.html#ModPForms.eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_heckePS_mem_modPMod.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.heckePS_mem_modPMod (N' : ℕ) [NeZero N'] (F : Type) [Field F]
    (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N' k F) :
    ModPForms.heckePS k ℓ φ ∈ ModPForms.modPMod N' k F := by sorry
