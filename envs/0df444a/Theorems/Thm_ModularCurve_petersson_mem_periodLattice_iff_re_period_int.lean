-- Prove2me | Theorems.Thm_ModularCurve_petersson_mem_periodLattice_iff_re_period_int
-- name    : ModularCurve.petersson_mem_periodLattice_iff_re_period_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/407c5574-9a76-5603-934a-a2caf224bb54
-- title:
--   i times the Petersson functional lies in the period lattice iff all periods have integral real part
-- statement:
--   Let $N\ge 1$ and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Write $\mathcal F_N = \bigcup_{q\in SL_2(\mathbb Z)/\Gamma_0(N)} (\mathrm{out}\,q)^{-1}\cdot\mathcal D$ for the union of the translates of the standard fundamental domain $\mathcal D$ of $SL_2(\mathbb Z)$ by the inverses of the chosen coset representatives, and let $\Lambda_N$ be the $\mathbb Z$-submodule of the $\mathbb C$-dual of $S_2(\Gamma_0(N))$ spanned by the functionals $\mathrm{period}_N(\gamma)$ for $\gamma\in\Gamma_0(N)$, where $\mathrm{period}_N(\gamma)$ sends a cusp form to $\int_0^1$ of the period integrand along the path from $i$ to $\gamma\cdot i$ (the functional [`ModularCurve.periodAlong N I (γ • I)`](def/ModularCurve_PeriodLattice.html#L78)). The assertion is the equivalence of two statements: (i) there exists $\Lambda\in\Lambda_N$ such that for every weight-$2$ cusp form $g$ for $\Gamma_0(N)$ one has $i\int_{\mathcal F_N} \mathrm{petersson}\,2\,f\,g\,(\tau) = \Lambda(g)$, the integral being taken with respect to the invariant measure on the upper half-plane; and (ii) for every $\gamma\in\Gamma_0(N)$ the real part of $\mathrm{period}_N(\gamma)(f)$ is an integer, i.e. equals $m$ for some $m\in\mathbb Z$.
--
--   This is the integrality criterion for the Riemann form on the period lattice of $X_0(N)$: the functional $i\langle\,\cdot\,,f\rangle$ built from the Petersson pairing with $f$ belongs to the lattice of periods exactly when all periods of $f$ have integral real part. It is used in the construction of the complex-analytic multiplier attached to a point of the Jacobian, notably by [`ModularCurve.multiplier_eq_exp_of_periodAlong_add_petersson_mem_periodLattice`](thm.html#ModularCurve.multiplier_eq_exp_of_periodAlong_add_petersson_mem_periodLattice) and by [`ModularCurve.ComplexPlaceDictionary.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_petersson_mem_periodLattice_iff_re_period_int.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.petersson_mem_periodLattice_iff_re_period_int
    {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    (∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = Λ g) ↔
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∃ m : ℤ, (ModularCurve.period N γ f).re = m := by sorry
