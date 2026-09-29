-- Prove2me | Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq
-- name    : ModularCurve.exists_cuspForm_petersson_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d076f644-fe0b-510d-8d2f-1072af88dc12
-- title:
--   Riesz representation for the weight-2 Petersson pairing
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $\ell$ be an element of the $\mathbb{C}$-linear dual of the space $S_2(\Gamma_0(N))$ of weight-$2$ cusp forms for the congruence subgroup $\Gamma_0(N)\le \mathrm{SL}_2(\mathbb{Z})$ (Mathlib's `CuspForm (CongruenceSubgroup.Gamma0 N) 2`). The assertion is that there exists a cusp form $f \in S_2(\Gamma_0(N))$ such that for every $g \in S_2(\Gamma_0(N))$ one has $$i\int_{\mathcal F_N} \mathrm{petersson}\,2\,f\,g\,(\tau)\, = \ell(g),$$ where the integrand is Mathlib's weight-$2$ Petersson integrand $\overline{f(\tau)}\,g(\tau)\,(\operatorname{Im}\tau)^{2}$, the integral is the Bochner integral over the upper half-plane with its measure, and the domain of integration is the fundamental set [`FLT.Gamma0FundamentalSet.gammaFundamentalSet`](def/AutomorphicForm_Gamma0FundamentalSet.html#L13) attached to $\Gamma_0(N)$, defined as the union, over all left cosets $q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_0(N)$, of the sets $(\mathrm{Quotient.out}\,q)^{-1}\cdot \mathcal D$, with $\mathcal D$ the standard closed fundamental domain $\{\tau : |\tau| \ge 1,\ |\operatorname{Re}\tau| \le 1/2\}$ for the full modular group and the translate taken for the action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathcal{H}$. Only existence of such an $f$ is asserted; no uniqueness, no integrability statement and no positivity of the pairing appear in the conclusion.
--
--   This is the surjectivity half of the Riesz-type identification of the dual of $S_2(\Gamma_0(N))$ with $S_2(\Gamma_0(N))$ itself via the Petersson pairing $g \mapsto i\langle g,f\rangle$, which rests on the finite-dimensionality of the space of cusp forms ([`CuspForm.finiteDimensional_Gamma0`](thm.html#CuspForm.finiteDimensional_Gamma0)). It serves the Abel–Jacobi and period-lattice description of $X_0(N)$, and is used by [`ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice) and by [`ModularCurve.petersson_mem_periodLattice_iff_re_period_int`](thm.html#ModularCurve.petersson_mem_periodLattice_iff_re_period_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cuspForm_petersson_eq.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq {N : ℕ} [NeZero N]
    (ℓ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = ℓ g := by sorry
