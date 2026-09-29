-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/edebd4eb-ea91-5916-95eb-26c29f0908d9
-- title:
--   Gauss lemma at the cusp: integrality over A[x'⁻¹]
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ but $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and assume $M/p \neq 0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (a fixed algebraic closure of $\mathbb{Q}$) with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of level $(M,H)$ inside $\overline{\mathbb{Q}}((q))$, and $F_{M/p}$ for the corresponding field at level $(M/p, \;H\cdot)$, the subgroup being the image of $H$ under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, and $\alpha : F_{M/p} \to F_M$ a $\overline{\mathbb{Q}}$-algebra map that is integral and preserves underlying Laurent series, so $\alpha u$ and $u$ have the same $q$-expansion. Let `Psp` be a place specialisation `JHPlaceSpecialization p M H hpM A` and `Rpd` a prolongation datum for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with the stated compatibilities. Let $x' \in F_{M/p}$ have $q$-expansion `jqModC`, the $j$-series over $\overline{\mathbb{Q}}$. Then for $\psi \in F_{M/p}$ such that $\alpha \psi$ lies in the valuation subring `Rpd.R₁.integers` of $F_M$, and such that $\psi$ lies in the valuation subring of every place $u_0$ of $F_{M/p}$ over $\overline{\mathbb{Q}}$ whose valuation subring contains $x'^{-1}$, the element $\psi$ belongs to `integralOverPoleChart A x'`, that is, $\psi$ is integral over the $A$-subalgebra $A[x'^{-1}]$ of $F_{M/p}$, where $A$ acts through $A \hookrightarrow \overline{\mathbb{Q}} \to F_{M/p}$.
--
--   This is the Gauss-lemma step at the cusp in level $M/p$: integrality of a function over the affine chart $A[x'^{-1}]$ around the pole of $x'$ is deduced from integrality of its image at level $M$ together with regularity at all places where $x'^{-1}$ is regular, using that an element lying in every valuation subring containing a ring is integral over it. It feeds the construction of the mod-$p$ model at the cusp, being cited by [`ModularCurve.XHDRModelAtP.exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (ψ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hψ : α ψ ∈ Rpd.R₁.integers)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), x'⁻¹ ∈ u₀.toValuationSubring → ψ ∈ u₀.toValuationSubring) :
    ψ ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by sorry
