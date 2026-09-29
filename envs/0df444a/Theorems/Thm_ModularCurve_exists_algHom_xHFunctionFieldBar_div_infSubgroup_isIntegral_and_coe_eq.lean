-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq
-- name    : ModularCurve.exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/7fba9fa4-4fbb-56d1-8496-5a4f7ef54918
-- title:
--   Degeneracy inclusion of ℚ̄-function fields of X_H
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $M/p$ nonzero, and let $H$ be a subgroup of $(\mathbb Z/M\mathbb Z)^\times$. Write $H' =$ `infSubgroup p M H hpM` for the image of $H$ in $(\mathbb Z/(M/p)\mathbb Z)^\times$ under the reduction map `ZMod.unitsMap` attached to the divisibility $(M/p) \mid M$. For a level $N$ and a subgroup $H''$ of $(\mathbb Z/N\mathbb Z)^\times$, `xHFunctionFieldBar N H''` denotes the intermediate field of $\overline{\mathbb Q} \subset \overline{\mathbb Q}((q))$ obtained as `laurentBaseChange`, i.e. the subfield generated over $\overline{\mathbb Q}$ by the image of the rational $q$-expansion function field `xHFunctionFieldC ℚ N H''` $\subset \mathbb Q((q))$ under the coefficientwise embedding `coeffEmb` of $\mathbb Q((q))$ into $\overline{\mathbb Q}((q))$. The assertion is that there exists a homomorphism $\alpha_H$ of $\overline{\mathbb Q}$-algebras from `xHFunctionFieldBar (M / p) H'` to `xHFunctionFieldBar M H` such that, first, the underlying ring homomorphism is integral (every element of the target is integral over the image), and second, $\alpha_H$ does not change $q$-expansions: for every $u$ in the source, the Laurent series in $\overline{\mathbb Q}((q))$ underlying $\alpha_H(u)$ equals the Laurent series underlying $u$.
--
--   This records, on the level of $q$-expansion function fields over $\overline{\mathbb Q}$, the degeneracy map $X_H(M) \to X_{H'}(M/p)$ that forgets the level-$p$ structure, normalised by the requirement that it be the identity on $q$-expansions. It is used in the analysis of the model of $X_H$ at $p$, in the construction of specialisations and prolongation data and in the comparison of valuation subrings with the Frobenius on $q$-expansions modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)] :
    ∃ (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)),
      αH.toRingHom.IsIntegral ∧
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by sorry
