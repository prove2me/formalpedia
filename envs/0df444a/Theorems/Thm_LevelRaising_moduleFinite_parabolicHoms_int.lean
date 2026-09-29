-- Prove2me | Theorems.Thm_LevelRaising_moduleFinite_parabolicHoms_int
-- name    : LevelRaising.moduleFinite_parabolicHoms_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/d820bde4-aa3d-50dc-ad06-f0335640609e
-- title:
--   Finite generation of integral parabolic homomorphisms on Γ₀(M)
-- statement:
--   Let $M$ be a natural number with $M \neq 0$. Consider the additive group $\mathrm{Hom}(\mathrm{Additive}\,\Gamma_0(M), \mathbb{Z})$ of additive monoid homomorphisms from the additivisation of the congruence subgroup $\Gamma_0(M) \le \mathrm{SL}_2(\mathbb{Z})$ to $\mathbb{Z}$, equivalently the group homomorphisms $\Gamma_0(M) \to \mathbb{Z}$, with its natural $\mathbb{Z}$-module structure. Inside it, [`ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 M) ℤ`](def/ModularCurve_PeriodMap.html#L62) is the $\mathbb{Z}$-submodule of those $\varphi$ which satisfy the parabolicity condition: $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(M)$ whose underlying integer matrix has trace with square equal to $4$, i.e. trace $\pm 2$. The theorem asserts that this submodule is a finite (finitely generated) $\mathbb{Z}$-module. Note that the vanishing condition is imposed on all elements of trace $\pm 2$, so it constrains $\varphi$ on $\pm$ unipotent elements of $\Gamma_0(M)$, and in particular on $-I$ when it lies in $\Gamma_0(M)$; no modular interpretation of these homomorphisms enters the statement.
--
--   Integral parabolic homomorphisms on $\Gamma_0(M)$ are the group-theoretic avatar of the integral parabolic cohomology of the modular curve $X_0(M)$, whose rank is $2g$ by Eichler–Shimura; only finite generation is recorded here. The result is used in the level-raising part of the argument, where it supplies the Noetherian hypothesis needed by [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LevelRaising_moduleFinite_parabolicHoms_int.lean

import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LevelRaising.moduleFinite_parabolicHoms_int (M : ℕ) [NeZero M] :
    Module.Finite ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 M) ℤ) := by sorry
