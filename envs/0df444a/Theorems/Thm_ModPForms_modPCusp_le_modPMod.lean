-- Prove2me | Theorems.Thm_ModPForms_modPCusp_le_modPMod
-- name    : ModPForms.modPCusp_le_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/2a6b5a76-3e75-57b6-90b7-fb717f4f81fd
-- title:
--   Mod-p cusp forms sit inside mod-p modular forms
-- statement:
--   Fix a natural number $N'$ that is nonzero, an integer weight $k$, and a field $F$. Two $F$-submodules of the formal power series ring $\mathrm{PowerSeries}\ F$ are in play. The first, `modPCusp N' k F`, is the $F$-span of the set of those power series $\varphi$ for which there exist a cusp form $f$ of weight $k$ for $\Gamma_0(N')$ and a sequence $a : \mathbb{N} \to \mathbb{Z}$ with $\mathrm{qCoeff}\, f\, n = (a\,n : \mathbb{C})$ for all $n$ — that is, the $n$-th coefficient of the $q$-expansion of $f$ at width $1$ equals the image of the integer $a\,n$ — and with $\varphi$ the power series whose $n$-th coefficient is the image of $a\,n$ in $F$. The second, `modPMod N' k F`, is the $F$-span of the same set of conditions with "cusp form" replaced by "modular form" of weight $k$ for $\Gamma_0(N')$. The assertion is the inclusion $\mathrm{modPCusp}\ N'\ k\ F \le \mathrm{modPMod}\ N'\ k\ F$ of submodules.
--
--   This records, at the level of the mod-$p$ spans of integral $q$-expansions, the inclusion of cusp forms into modular forms of the same weight and level. It is used throughout the mod-$p$ forms part of the development, for instance when results proved for spans of integral modular forms are applied to cusp forms, and in the analysis of the Hecke algebra acting on mod-$p$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPCusp_le_modPMod.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPCusp_le_modPMod (N' : ℕ) [NeZero N'] (k : ℤ) (F : Type) [Field F] :
    modPCusp N' k F ≤ modPMod N' k F := by sorry
