-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_levelAut_sub_mem_of_isLevelAutAt_of_mem_Gamma_of_mem_ssJSet_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.levelAut_sub_mem_of_isLevelAutAt_of_mem_Gamma_of_mem_ssJSet_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/e5ed3d68-5569-57f0-a470-fe2d5d608a82
-- title:
--   Level automorphisms fix supersingular points of the finite j-chart
-- statement:
--   Fix primes $q \ge 5$ and $\ell \ge 3$ with $\ell \neq q$, and $M' \neq 0$ divisible by neither $q$ nor $\ell$. Let $L$ be a characteristic-zero field that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with $\zeta \in L$ a primitive $q$-th and $\xi \in L$ a primitive $(q\ell)$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of level $N_0 = (q\ell)^2 M'$ attached to the subgroup $H = \ker\bigl((\mathbb{Z}/N_0)^\times \to (\mathbb{Z}/q\ell)^\times\bigr)$ of units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, together with an $A$-algebra structure on $K$ compatible with $L$; let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be the element whose Laurent series is the coefficientwise image of the $q$-expansion $j_q$ of the modular $j$-function, assumed nonzero, and let $C = \mathrm{chartAlgFin}\,A\,K\,j$ be the subalgebra of elements of $K$ integral over $A[j]$. Consider the two-chart integral model $X = \mathrm{TwoChartIntegralModel}\,A\,K\,j$, the pushout gluing $\operatorname{Spec} C$ to the chart attached to $j^{-1}$, let $z$ be a point of $X$ at which the germ of the global section coming from $\varpi$ along the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk, and let $y$ be a point of $\operatorname{Spec} C$ mapping to $z$ under the canonical morphism `ιFin`. Assume $y$ is supersingular in the following sense: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel the prime $y$, the element $\varphi(j)$ lies in $\mathrm{ssJSet}\,q\,\Omega$, that is, every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. The conclusion is: for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and in $\Gamma(\ell)$, every $L$-algebra automorphism $\tau$ of $K$ satisfying $\mathrm{IsLevelAutAt}\,L\,(q\ell)\,\xi\,(q\ell)\,N_0\,H\,\gamma^{-1}\,K\,\tau$ — i.e. for all weights $k$, all weight-$k$ modular forms $f, g$ for $\Gamma_H(N_0)$ with integral $q$-expansions $p_f, p_g$, $p_g$ giving a nonzero series, all $x \in K$ whose Laurent series is the coefficientwise image of the ratio of the two series, and every embedding $\iota : L \to \mathbb{C}$ with $\iota(\xi) = e^{2\pi i/(q\ell)}$, one has $\iota_*(\tau x) \cdot q\mathrm{Exp}(g \mid_k \mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}) = q\mathrm{Exp}(f \mid_k \mathrm{conjElemN}\,(q\ell)\,\gamma^{-1})$ — and every proof that $\tau$ maps $C$ into $C$, the induced endomorphism of $C$ satisfies $\tau(a) - a \in y$ for all $a \in C$.
--
--   This is the statement that a level automorphism attached to $\gamma \in \Gamma_0(M') \cap \Gamma(\ell)$ acts as the identity on the residue data at a supersingular point of the special fibre of the two-chart integral model of the modular curve, the arithmetic input going back to the theory of supersingular points on integral models of modular curves. It is used by [`ModularCurve.FullLevel.AuxLevel.levelAut_mem_chartAlgFin_and_sub_mem_of_isLevelAutAt_of_mem_ssJSet_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.levelAut_mem_chartAlgFin_and_sub_mem_of_isLevelAutAt_of_mem_ssJSet_twoChartIntegralModel), which combines it with the statement that $\tau$ preserves the finite chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_levelAut_sub_mem_of_isLevelAutAt_of_mem_Gamma_of_mem_ssJSet_twoChartIntegralModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.levelAut_sub_mem_of_isLevelAutAt_of_mem_Gamma_of_mem_ssJSet_twoChartIntegralModel
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal := by sorry
