-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
-- name    : ModularCurve.DRModel.exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7573a289-6717-563f-9abc-7a16361a0ed8
-- title:
--   Pole-chart lift of 1/̄ jₚ on the W₁ branch
-- statement:
--   Let $p$ be a prime and let $F =$ `modularFunctionFieldFull p` be the subfield of $\mathbf{Q}((q))$ (Laurent series over $\mathbf{Q}$) generated over $\mathbf{Q}$ by the divisor expansions of level $p$, containing the element $j =$ `IgusaScheme.jFull p` given by the $q$-expansion `jq`. Write $A_{\mathrm{fin}}$ for `chartAlgFin ℤ F j`, the subalgebra of elements of $F$ integral over $\mathbf{Z}[j]$, and $A_\infty$ for `chartAlgInf ℤ F j`, the elements integral over $\mathbf{Z}[j^{-1}]$. Assume given $j_p \in A_{\mathrm{fin}}$ whose Laurent expansion is the image of `jq` under the substitution $q \mapsto q^p$ on exponents, and two distinct valuation subrings $W_0 \neq W_1$ of $F$ such that $p$ lies in the set of nonunits of each; that for $i \in \{0,1\}$ and every $P \in \mathbf{Z}[X]$ with nonzero reduction mod $p$ both $P(j)$ and $P(j)^{-1}$ lie in $W_i$; that every valuation subring $V$ of $F$ with $p$ among its nonunits and with the same inversion property for such $P(j)$ equals $W_0$ or $W_1$; that $j_p - j^p$ is a nonunit of $W_0$; that every $x \in W_0$ satisfies $x\,Q(j) - P(j) \in W_0^{\times c}$ (the nonunits of $W_0$) for some $P, Q \in \mathbf{Z}[X]$ with $Q$ nonzero mod $p$, and that every $x \in W_1$ satisfies $x\,Q(j_p) - P(j_p)$ a nonunit of $W_1$ for some such $P, Q$. Assume further an ideal $\mathfrak{p}_1$ of $A_{\mathrm{fin}}$ whose elements are exactly those mapping into the nonunits of $W_1$, together with a ring isomorphism $e_1 : A_{\mathrm{fin}}/\mathfrak{p}_1 \cong (\mathbf{Z}/p)[X]$ sending the class of $j_p$ to $X$ and the class of $j$ (as the element `jChartFin`) to $X^p$. Then there exists $b' \in A_\infty$ with $b' j_p - 1$ a nonunit of $W_1$.
--
--   This is the ring-theoretic form, on the chart at $j = \infty$ over $\mathbf{Z}$, of the statement that on the Frobenius-twisted component of the mod-$p$ fibre of the Deligne–Rapoport model of $X_0(p)$ the inverse of the residue of $j_p$ is already represented by a function integral over $\mathbf{Z}[j^{-1}]$. It is the arithmetic input to [`ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair`](thm.html#ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair), and it is proved from the mutual localisation property of the two pole charts attached to $j$ and to $j_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve Polynomial

theorem ModularCurve.DRModel.exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
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
    ∃ b' : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), (b' : ↥(modularFunctionFieldFull p)) * (jp : ↥(modularFunctionFieldFull p)) - 1 ∈ W₁.nonunits := by sorry
