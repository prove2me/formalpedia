-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq
-- name    : ModularCurve.DRModel.exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/99e86504-77ef-5b3a-b8ac-5be8dc80b31a
-- title:
--   Involution over ℤ of the two-chart model of X₀(p)
-- statement:
--   Let $p\ge 5$ be a prime and let $F$ denote `modularFunctionFieldFull p`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $p$, with distinguished element $j =$ `IgusaScheme.jFull p`, the element whose Laurent series is `jq`. Write $A_{\mathrm{fin}}$ and $A_\infty$ for the subalgebras `chartAlgFin` and `chartAlgInf` of $F$, consisting of the elements of $F$ integral over $\mathbb{Z}[j]$, respectively over $\mathbb{Z}[j^{-1}]$, and `DRModel p` for the two-chart model, the pushout of $\operatorname{Spec}$ of the inclusions of $A_{\mathrm{fin}}$ and $A_\infty$ into $\mathbb{Z}[j,j^{-1}]$-integral elements, with structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb{Z}$. The data are: an element $j_p\in A_{\mathrm{fin}}$ whose Laurent series is $\mathrm{qExpand}_{\mathbb{Q}}(p)$ applied to `jq`; two distinct valuation subrings $W_0,W_1$ of $F$, each having $p$ among its nonunits, such that for each $i$ and each $P\in\mathbb{Z}[X]$ with $P\bmod p\ne 0$ both $P(j)$ and $P(j)^{-1}$ lie in $W_i$, and such that every valuation subring $V$ of $F$ with $p$ a nonunit and with this same property for $j$ equals $W_0$ or $W_1$; the condition $j_p-j^p\in\mathfrak{m}_{W_0}$; residue-generation clauses, namely that every $x\in W_0$ satisfies $x\,Q(j)-P(j)\in\mathfrak{m}_{W_0}$ for some $P,Q\in\mathbb{Z}[X]$ with $Q\bmod p\ne0$, and likewise every $x\in W_1$ satisfies $x\,Q(j_p)-P(j_p)\in\mathfrak{m}_{W_1}$ for such $P,Q$; and a $\mathbb{Z}$-algebra homomorphism $\varphi\colon A_\infty\to\mathbb{Z}$ whose value on each $x$ is, in $\mathbb{Q}$, the coefficient of $q^0$ in the Laurent expansion of $x$. The conclusion asserts the existence of an isomorphism $w$ of `DRModel p` with itself such that $w$ followed by `DRModel.toBase p` is `DRModel.toBase p`, such that $w$ followed by $w$ is the identity, and such that for some $\mathbb{Z}$-algebra homomorphism $\psi_0\colon A_\infty\to\mathbb{Z}$ one has: $\operatorname{Spec}\varphi$ followed by the chart morphism `ιInf` and then by $w$ equals $\operatorname{Spec}\psi_0$ followed by `ιInf`; $p\mid\psi_0(a)$ for every $a\in A_\infty$ lying in the nonunits of $W_1$; and there is some $a\in A_\infty$ lying in the nonunits of $W_0$ with $p\nmid\psi_0(a)$.
--
--   This is the Atkin–Lehner involution $w_p$ of the Deligne–Rapoport two-chart integral model of $X_0(p)$ over $\mathbb{Z}$, obtained as the composite of the comparison isomorphism between the models built from $j$ and from $j_p$ with the transport isomorphism coming from the swap of the two generators, together with the statement that $w$ carries the $\mathbb{Z}$-point $\infty$ of the pole chart to a $\mathbb{Z}$-point reducing into the component indexed by $W_1$ rather than $W_0$. It feeds the construction of the pinned model package in [`ModularCurve.exists_dRModelPackage_ffPin`](thm.html#ModularCurve.exists_dRModelPackage_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
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
    (φ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ).coeff 0) :
    ∃ w : DRModel p ≅ DRModel p,
      w.hom ≫ DRModel.toBase p = DRModel.toBase p ∧
      w.hom ≫ w.hom = 𝟙 (DRModel p) ∧
      ∃ ψ₀ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ,
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
              TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ≫ w.hom =
          Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫
            TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
        (∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
            (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ₀ a) ∧
        (∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
            (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ₀ a) := by sorry
