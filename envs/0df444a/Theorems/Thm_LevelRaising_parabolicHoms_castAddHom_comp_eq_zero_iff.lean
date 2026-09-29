-- Prove2me | Theorems.Thm_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff
-- name    : LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/d8aaea84-c577-5c85-a6e0-2b9e38aeee96
-- title:
--   p-saturation of integral parabolic period homomorphisms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ and let $p$ be a natural number (no primality is assumed). Let $x$ be an element of the $\mathbb Z$-submodule [`ModularCurve.Period.parabolicHoms ℤ Γ ℤ`](def/ModularCurve_PeriodMap.html#L62) of $\mathrm{Hom}(\mathrm{Additive}\,\Gamma,\mathbb Z)$, that is, an additive homomorphism $x$ from $\Gamma$ written additively to $\mathbb Z$ satisfying the predicate `IsParabolicHom`: $x(\gamma)=0$ for every $\gamma\in\Gamma$ whose underlying $2\times 2$ integer matrix has $(\mathrm{tr}\,\gamma)^2=4$. The assertion is an equivalence: the composite of $x$ with the reduction map $\mathbb Z\to\mathbb Z/p$ (as an additive group homomorphism) is the zero homomorphism if and only if there exists $x'$ in [`ModularCurve.Period.parabolicHoms ℤ Γ ℤ`](def/ModularCurve_PeriodMap.html#L62) with $x=p\cdot x'$, the scalar $p$ being taken in $\mathbb Z$. Thus divisibility by $p$ of all values of $x$ already forces divisibility by $p$ inside the module of parabolic homomorphisms. For $p=0$ the statement degenerates to the equivalence of $x=0$ with itself.
--
--   This is the saturation property of the lattice of integral parabolic (cuspidal) period homomorphisms inside the lattice of all integral homomorphisms on $\Gamma$, in the form used when comparing integral modular symbols with their reductions modulo $p$. It is invoked in the level-raising and Ihara-type arguments of the project, notably for eigenclasses modulo $p$ and for the support of $q$-new parts at an odd prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff.lean

import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} {p : ℕ}
    (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) :
    (Int.castAddHom (ZMod p)).comp (x : Additive Γ →+ ℤ) = 0
      ↔ ∃ x' : ModularCurve.Period.parabolicHoms ℤ Γ ℤ, x = (p : ℤ) • x' := by sorry
