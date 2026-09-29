-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
-- name    : ModularCurve.DRModel.exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/621fa28d-9ecf-5603-8211-3bf2d9438f87
-- title:
--   An involution of the two-chart model X₀(p) over ℤ
-- statement:
--   Let $p$ be a prime with $5 \le p$, write $F =$ `modularFunctionFieldFull p` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions at level $p$, and let $j =$ `IgusaScheme.jFull p` be the element of $F$ given by the Laurent series `jq`. Let $A_{\mathrm{fin}}$ and $A_\infty$ denote `chartAlgFin` and `chartAlgInf`, the subalgebras of elements of $F$ integral over $\mathbb{Z}[j]$, resp. over $\mathbb{Z}[j^{-1}]$, and let `DRModel p` be the pushout scheme glued from $\operatorname{Spec} A_{\mathrm{fin}}$ and $\operatorname{Spec} A_\infty$, with structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb{Z}$. Assume given: an element $j_p \in A_{\mathrm{fin}}$ whose Laurent series is `qExpand ℚ p jq` (substitution $q \mapsto q^p$ in `jq`); two distinct valuation subrings $W_0 \ne W_1$ of $F$ in which $p$ is a nonunit, such that for $i \in \{0,1\}$ and every $P \in \mathbb{Z}[X]$ with $P \bmod p \ne 0$ both $P(j)$ and $P(j)^{-1}$ lie in $W_i$, and such that every valuation subring $V$ of $F$ with $p \in V^{\mathrm{nu}}$ having this last property equals $W_0$ or $W_1$; the condition $j_p - j^p \in W_0^{\mathrm{nu}}$; residue-generation clauses saying that each $x \in W_0$ satisfies $x\,Q(j) - P(j) \in W_0^{\mathrm{nu}}$ for some $P, Q \in \mathbb{Z}[X]$ with $Q \bmod p \ne 0$, and each $x \in W_1$ satisfies $x\,Q(j_p) - P(j_p) \in W_1^{\mathrm{nu}}$ for such $P,Q$; and a $\mathbb{Z}$-algebra homomorphism $\varphi : A_\infty \to \mathbb{Z}$ whose value on $x$ is the $0$th Laurent coefficient of $x$. Then there exist an isomorphism $w$ of `DRModel p` with itself and a $\mathbb{Z}$-algebra endomorphism $\theta$ of $A_{\mathrm{fin}}$ such that: $w$ followed by `DRModel.toBase p` is `DRModel.toBase p`; $w$ composed with itself is the identity of `DRModel p`; the chart immersion `ιFin` followed by $w$ equals $\operatorname{Spec}(\theta)$ followed by `ιFin`; $\theta(\theta x) = x$ for all $x$; for all $x$, $\theta x \in W_1$ if and only if $x \in W_0$; $\theta$ sends `jChartFin` (the element $j$ of $A_{\mathrm{fin}}$) to $j_p$; and there is a $\mathbb{Z}$-algebra homomorphism $\psi_0 : A_\infty \to \mathbb{Z}$ with $(\operatorname{Spec}(\varphi)$ followed by `ιInf`$)$ followed by $w$ equal to $\operatorname{Spec}(\psi_0)$ followed by `ιInf`, with $p \mid \psi_0(a)$ for every $a \in A_\infty$ whose image in $F$ lies in $W_1^{\mathrm{nu}}$, and with some $a \in A_\infty$ whose image lies in $W_0^{\mathrm{nu}}$ and $p \nmid \psi_0(a)$.
--
--   This is the Atkin–Lehner involution $w_p$ of the Deligne–Rapoport model of $X_0(p)$ over $\mathbb{Z}$, realised on the two-chart model built from $j$, together with the data of its action on the finite chart (the $\mathbb{Z}$-algebra endomorphism $\theta$ exchanging the two valuation rings above $p$ and sending $j$ to $j_p$) and on the cusp $\infty$ (the translated $\mathbb{Z}$-point $\psi_0$, which lands in the $W_0$-component of the fibre at $p$). It is used to show that the fibre at $p$ contains a point outside the finite chart, in [`ModularCurve.DRModel.exists_ne_and_notMem_chartFin_pFibre`](thm.html#ModularCurve.DRModel.exists_ne_and_notMem_chartFin_pFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
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
    ∃ (w : DRModel p ≅ DRModel p) (θ : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))),
      w.hom ≫ DRModel.toBase p = DRModel.toBase p ∧
      w.hom ≫ w.hom = 𝟙 (DRModel p) ∧
      TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ≫ w.hom =
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
      (∀ x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), θ (θ x) = x) ∧
      (∀ x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
          ((θ x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) ∈ W₁ ↔
            ((x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) ∈ W₀) ∧
      ((θ (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) :
          ↥(modularFunctionFieldFull p)) = (jp : ↥(modularFunctionFieldFull p)) ∧
      ∃ ψ₀ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ,
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
              TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ≫ w.hom =
          Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫
            TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
        (∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
            (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ₀ a) ∧
        (∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
            (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ₀ a) := by sorry
