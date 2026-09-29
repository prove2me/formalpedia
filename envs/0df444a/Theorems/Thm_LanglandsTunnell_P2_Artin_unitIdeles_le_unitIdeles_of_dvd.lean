-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd
-- name    : LanglandsTunnell.P2.Artin.unitIdeles_le_unitIdeles_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/2fcc6883-857b-5e0c-b618-a833e8c98dc4
-- title:
--   Monotonicity of unit idèle congruence subgroups in the level
-- statement:
--   Let $F$ be a number field and let $\mathfrak m, \mathfrak m'$ be ideals of the ring of integers $\mathcal O_F$ with $\mathfrak m' \neq \bot$ and $\mathfrak m \mid \mathfrak m'$. For an ideal $\mathfrak f$ of $\mathcal O_F$, the subgroup `unitIdeles F 𝔣` of the unit group of the adèle ring of $F$ consists of those idèles $u$ whose finite part (the image of $u$ under `projFin`) satisfies: the valuation of its component at every finite place $v$ of $F$ equals $1$; for every finite place $v$ with $v.asIdeal \mid \mathfrak f$, the valuation of (component at $v$) $-\,1$ is at most $\exp(-n_v)$, where $n_v$ is the multiplicity with which $v.asIdeal$ occurs in $\mathfrak f$; and, for every ring homomorphism $\tau : F \to \mathbb R$, the predicate `archSign F τ u` holds, i.e. the real number $\mathtt{archRealProjTau}\ F\ \tau\ u$ is positive. The assertion is the inclusion of subgroups $\mathtt{unitIdeles}\ F\ \mathfrak m' \le \mathtt{unitIdeles}\ F\ \mathfrak m$: every unit idèle of level $\mathfrak m'$ is a unit idèle of level $\mathfrak m$.
--
--   This is the standard antitonicity of the congruence subgroups $U_{\mathfrak m}$ of the idèle group in the modulus: a deeper level imposes stronger congruences. It is used to transport membership statements about unit idèles from a level $\mathfrak m$ to any multiple of it, and is cited in the proof of [`NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm`](thm.html#NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.unitIdeles_le_unitIdeles_of_dvd
    (F : Type*) [Field F] [NumberField F] {𝔪 𝔪' : Ideal (𝓞 F)} (h' : 𝔪' ≠ ⊥) (h : 𝔪 ∣ 𝔪') :
    unitIdeles F 𝔪' ≤ unitIdeles F 𝔪 := by sorry
