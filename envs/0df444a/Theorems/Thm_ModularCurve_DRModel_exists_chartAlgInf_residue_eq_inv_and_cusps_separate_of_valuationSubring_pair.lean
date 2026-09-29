-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair
-- name    : ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/57bba821-f10d-54c0-921a-c0dfbdde7a15
-- title:
--   Pole-chart residue X⁻¹ and separation of the two cusps
-- statement:
--   Fix a prime $p$ and write $F$ for the field `modularFunctionFieldFull p` (the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions at level $p$) and $j$ for `IgusaScheme.jFull p`, the element of $F$ with $q$-expansion `jq`. Let $A_{\mathrm{fin}}$ and $A_\infty$ be the chart algebras `TwoChartIntegralModel.chartAlgFin ℤ F j` and `chartAlgInf ℤ F j`, consisting of the elements of $F$ integral over $\mathbb{Z}[j]$, resp. over $\mathbb{Z}[j^{-1}]$, and let `jInvChartInf` denote $j^{-1}\in A_\infty$. Assume given: $j_p\in A_{\mathrm{fin}}$ whose Laurent expansion is `qExpand ℚ p jq` (the substitution $q\mapsto q^{p}$ applied to `jq`); two distinct valuation subrings $W_0\ne W_1$ of $F$ in each of which $p$ is a non-unit; for $i\in\{0,1\}$, the condition that $P(j)$ and $P(j)^{-1}$ both lie in $W_i$ for every $P\in\mathbb{Z}[X]$ with nonzero reduction mod $p$; completeness of the pair, i.e. every valuation subring $V$ of $F$ in which $p$ is a non-unit and which has the same inversion property equals $W_0$ or $W_1$; that $j_p-j^{p}$ is a non-unit of $W_0$; residue-generation clauses saying every $x\in W_0$ (resp. $x\in W_1$) satisfies $x\,Q(j)-P(j)\in W_0^{\mathrm{nonunits}}$ (resp. $x\,Q(j_p)-P(j_p)\in W_1^{\mathrm{nonunits}}$) for some $P,Q\in\mathbb{Z}[X]$ with $Q$ nonzero mod $p$; an ideal $\mathfrak p_1\subseteq A_{\mathrm{fin}}$ whose members are exactly the elements lying in the non-units of $W_1$; and a ring isomorphism $e_1\colon A_{\mathrm{fin}}/\mathfrak p_1\xrightarrow{\sim}\mathbb{Z}/p[X]$ with $e_1(\bar j_p)=X$ and $e_1(\bar j)=X^{p}$. The conclusion is twofold: first, there are $b'\in A_\infty$, $n\in\mathbb{N}$ and $b\in A_{\mathrm{fin}}$ with $b=b'\,j^{n}$ in $F$ and $e_1(\bar b)\cdot X=X^{pn}$ in $\mathbb{Z}/p[X]$; second, there are $a_0,a_1,c\in A_\infty$ with $a_0$ a non-unit of $W_0$, $a_1$ a non-unit of $W_1$, and $a_0+a_1+c\,j^{-1}=1$.
--
--   The two assertions are the inputs needed for the description of the mod-$p$ fibre of the Deligne–Rapoport model of $X_0(p)$ as two rational curves: the first makes the residue map of the pole chart on the Frobenius-twisted component attain $X^{-1}$, and the second expresses that the centres of the two cusps together with $j^{-1}$ generate the unit ideal of $A_\infty$, so that the cusps lie on different components and all crossings occur in the finite chart. It is used by [`ModularCurve.DRModel.exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton`](thm.html#ModularCurve.DRModel.exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton), by [`ModularCurve.DRModelPackage.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing`](thm.html#ModularCurve.DRModelPackage.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing), and by the related closed-immersion statements for the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve Polynomial

theorem ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits)
    (𝔭₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (h𝔭₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
        a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits))
    (e₁ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+* Polynomial (ZMod p))
    (he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X)
    (he₁j : e₁ (Ideal.Quotient.mk 𝔭₁ (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X ^ p) :

    (∃ (b' : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (n : ℕ)
        (b : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))),
        (b : ↥(modularFunctionFieldFull p)) = (b' : ↥(modularFunctionFieldFull p)) * (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ n ∧
        e₁ (Ideal.Quotient.mk 𝔭₁ b) * X = X ^ (p * n)) ∧

    (∃ (a₀ a₁ c : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))),
        (a₀ : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ (a₁ : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ∧
        a₀ + a₁ + c * TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) = 1) := by sorry
