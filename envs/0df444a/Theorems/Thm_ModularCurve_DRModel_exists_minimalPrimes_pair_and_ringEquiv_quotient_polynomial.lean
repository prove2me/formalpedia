-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
-- name    : ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/579c3987-50bb-54d7-aa62-49a812cc871f
-- title:
--   Special fibre of X₀(p) on the finite chart
-- statement:
--   Let $p$ be a prime (and nonzero as a natural number), let $F$ be the field $\mathbb{Q}$-generated inside $\mathrm{LaurentSeries}\,\mathbb{Q}$ by the divisor expansions of level $p$, let $j\in F$ be the element given by the series $jq$, and let $A\subseteq F$ be the subalgebra of elements integral over $\mathbb{Z}[j]$ (the finite chart of the two-chart integral model). Let $jp\in A$ have Laurent series $\mathrm{qExpand}\,\mathbb{Q}\,p\,jq$, i.e. $j(q^p)$. Let $W_0\neq W_1$ be valuation subrings of $F$ in each of which $p$ is a non-unit, such that for every $P\in\mathbb{Z}[X]$ with nonzero reduction mod $p$ both $P(j)$ and $P(j)^{-1}$ lie in $W_0$ and in $W_1$, and such that any valuation subring $V$ of $F$ with $p$ a non-unit and with the same property on $P(j)$ and $P(j)^{-1}$ equals $W_0$ or $W_1$. Assume $jp-j^{p}$ lies in the maximal ideal of $W_0$; assume every $x\in W_0$ satisfies $xQ(j)-P(j)\in\mathfrak{m}_{W_0}$ for some $P,Q\in\mathbb{Z}[X]$ with $Q$ nonzero mod $p$, and every $x\in W_1$ satisfies $xQ(jp)-P(jp)\in\mathfrak{m}_{W_1}$ likewise. Then there are ideals $\mathfrak{p}_0,\mathfrak{p}_1$ of $A$ with $\mathfrak{p}_i=A\cap\mathfrak{m}_{W_i}$ elementwise, $\mathfrak{p}_0\neq\mathfrak{p}_1$, the minimal primes of $pA$ being exactly $\{\mathfrak{p}_0,\mathfrak{p}_1\}$, and ring isomorphisms $A/\mathfrak{p}_0\cong\mathbb{F}_p[X]$ sending $j\mapsto X$, $jp\mapsto X^{p}$, and $A/\mathfrak{p}_1\cong\mathbb{F}_p[X]$ sending $jp\mapsto X$, $j\mapsto X^{p}$.
--
--   This is the ring-theoretic form, on the finite ($j$-integral) chart, of the Deligne–Rapoport description of the special fibre of $X_0(p)$ at $p$: two copies of the $j$-line crossing, the two branches being the graphs of Frobenius in the two directions, with the branch centres realised as the contractions of the maximal ideals of the two branch valuation rings. It feeds the downstream statements about the integral model package, in particular those locating germs and ranges in the zero locus of $j(q^p)-j(q)^p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve Polynomial
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
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
            ∈ W₁.nonunits) :
    let A := TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    let j : ↥A := TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    ∃ 𝔭₀ 𝔭₁ : Ideal ↥A,
      (∀ a : ↥A, a ∈ 𝔭₀ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)) ∧
      (∀ a : ↥A, a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)) ∧
      (Ideal.span {((p : ℕ) : ↥A)}).minimalPrimes = {𝔭₀, 𝔭₁} ∧ 𝔭₀ ≠ 𝔭₁ ∧
      (∃ e₀ : (↥A ⧸ 𝔭₀) ≃+* Polynomial (ZMod p),
          e₀ (Ideal.Quotient.mk 𝔭₀ j) = X ∧ e₀ (Ideal.Quotient.mk 𝔭₀ jp) = X ^ p) ∧
      (∃ e₁ : (↥A ⧸ 𝔭₁) ≃+* Polynomial (ZMod p),
          e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X ∧ e₁ (Ideal.Quotient.mk 𝔭₁ j) = X ^ p) := by sorry
