-- Prove2me | Theorems.Thm_ModPForms_heckePS_mem_modPCusp
-- name    : ModPForms.heckePS_mem_modPCusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/43d09fb7-e1c6-590c-bc74-6ce096016c30
-- title:
--   T_ℓ stability of mod-p cusp forms
-- statement:
--   Let $N'\ge 1$ be a natural number, $F$ a field, $k$ an integer, and $\ell$ a natural number that is prime and does not divide $N'$. Write $\widetilde S_k(N';F)$ for the $F$-submodule [`ModPForms.modPCusp N' k F`](def/CuspForm_ModPForms.html#L7) of $F[[q]]$, namely the $F$-span of all power series $\sum_n \overline{a_n}\,q^n$ obtained from a cusp form $f$ of weight $k$ on $\Gamma_0(N')$ together with a sequence $a:\mathbb{N}\to\mathbb{Z}$ such that the $n$-th coefficient of the width-one $q$-expansion of $f$ equals $a_n$ for every $n$, the coefficients of the power series being the images of the $a_n$ in $F$. Let $\varphi$ be a power series over $F$ lying in $\widetilde S_k(N';F)$. The conclusion is that [`ModPForms.heckePS k ℓ φ`](def/CuspForm_ModPForms.html#L20) again lies in $\widetilde S_k(N';F)$, where `heckePS k ℓ φ` is the power series whose $n$-th coefficient is $$\varphi_{n\ell} + \begin{cases}(\ell)^{k-1}\,\varphi_{n/\ell} & \ell \mid n,\\ 0 & \text{otherwise},\end{cases}$$ the power $(\ell:F)^{k-1}$ being an integer power in the field $F$.
--
--   This is the statement that the $q$-expansion formula for the Hecke operator $T_\ell$ at a prime $\ell$ not dividing the level preserves the space of mod-$p$ cusp forms of level $N'$ and weight $k$, i.e. the $F$-span of reductions of integrally-normalised cusp forms on $\Gamma_0(N')$. It supplies the Hecke-module structure on these spaces used in the supersingular-points argument, and is cited by [`ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit`](thm.html#ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_heckePS_mem_modPCusp.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.heckePS_mem_modPCusp (N' : ℕ) [NeZero N'] (F : Type) [Field F]
    (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp N' k F) :
    ModPForms.heckePS k ℓ φ ∈ ModPForms.modPCusp N' k F := by sorry
