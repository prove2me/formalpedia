-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin
-- name    : ModularCurve.XHDRModelAtP.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/5f114060-caaa-5a74-944d-88a42455b135
-- title:
--   Generic unramifiedness of the Γ_H chart ring over Rₚ[X]
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the whole kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, i.e. every unit sent to $1$ by `ZMod.unitsMap` along $(M/p) \mid M$ lies in $H$. Assume the $q$-expansion $j$-series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤`, and fix a term $\mathfrak{X}$ of the structure `XHDRModelAtP p M H hpM hj`, which packages the two-chart integral model of the $\Gamma_H$-curve over the base ring `R p` (a subring of $\mathbb{Q}$ with fraction field $\mathbb{Q}$) together with its properness, flatness, integrality, local finite presentation and normality, the smoothness of the auxiliary $\Gamma_N$-model, a curve model over $\overline{\mathbb{Q}}$ identified with the geometric fibre compatibly with Galois action and with $q$-expansions, and generic smoothness and geometric integrality. Let $v$ belong to `chartAlgFin p (ΓM M H) hj`, the subalgebra of elements of the $q$-expansion field of $\Gamma_H(M)$ that are integral over $(R\,p)[j]$, and suppose the Laurent series underlying $v$ is either `modularUnitSeries p` $= \Delta(q)/\Delta(q^p)$ or $p^{12}$ times its inverse. Give `chartAlgFin p (ΓM M H) hj` the $(R\,p)[X]$-algebra structure sending $X \mapsto v$. The assertion is that there exists a nonzero $c_0' \in \mathbb{Z}[X]$ such that for every prime ideal $P$ of `chartAlgFin p (ΓM M H) hj` whose contraction along $R\,p \to$ `chartAlgFin` is the zero ideal and with $c_0'(v) \notin P$, the algebra `chartAlgFin p (ΓM M H) hj` is unramified over $(R\,p)[X]$ at $P$.
--
--   This is the characteristic-zero half of the assertion that the $\Gamma_H$-chart ring is generically étale over the rational function field in Ogg's modular unit $\Delta(q)/\Delta(q^p)$: primes lying over the generic point of $\operatorname{Spec} R\,p$ and avoiding one fixed discriminant-type value $c_0'(v)$ are unramified. It feeds [`ModularCurve.XHDRModelAtP.exists_finite_etale_quotient_span_aeval_chartAlgFin`](thm.html#ModularCurve.XHDRModelAtP.exists_finite_etale_quotient_span_aeval_chartAlgFin), where the generic and special fibre information are combined into a finite étale quotient statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel Polynomial
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹) :
    letI : Algebra (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) := (Polynomial.aeval (R := R p) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [P.IsPrime],
      P.comap (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt (R p)[X] P := by sorry
