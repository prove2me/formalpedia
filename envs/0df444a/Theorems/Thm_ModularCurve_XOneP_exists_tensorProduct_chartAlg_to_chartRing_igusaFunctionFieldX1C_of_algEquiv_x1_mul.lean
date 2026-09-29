-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_of_algEquiv_x1_mul
-- name    : ModularCurve.XOneP.exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_of_algEquiv_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/50e1bba7-0b58-5cb1-8a4f-58b04cd0e84c
-- title:
--   Integral j-charts map to the Igusa curve through σ
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq L((q))$ obtained by adjoining to $L$ the coefficientwise image under $\mathrm{coeffEmb}\,L$ of the function field `x1FunctionField (M * p)`, let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$ be the element whose Laurent expansion is the image of $jq=q^{-1}\cdot\mathrm{jNumQ}(q)$, assumed non-zero. Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, and $w$ an integral weight-one form of level $M$ over $k$: a modular form of weight $1$ on $\Gamma_1(M)$ together with a power series over $\mathbb{Z}$ realising its $q$-expansion, whose reduction $\mathrm{intSeriesC}\,k$ is non-zero. Let $\sigma$ be an $L$-algebra automorphism of $K$ such that the Laurent expansion of $\sigma(j)$ is the image of $\mathrm{qExpand}\,\mathbb{Q}\,p\,(jq)$, i.e. $j(q^{p})$; such that $b$ lies in the finite chart algebra `chartAlgFin A ↥K j` if and only if $\sigma(b)$ does; and such that, for every valuation subring $W_0$ of $K$ characterised by $f\in W_0\iff$ there are $x,y\in A[[q]]$ with $y\not\equiv 0$ modulo the maximal ideal and $f\cdot y=x$ in $L((q))$ (the Gauss valuation ring), the comap $\sigma^{-1}W_0$ differs from $W_0$ and contains both $P(j)$ and $P(j)^{-1}$ for every polynomial $P$ over $A$ with non-zero reduction. The conclusion asserts the existence of an element $t$ of the Igusa function field $\mathrm{igusaFunctionFieldX1C}\,k\,M\,w\subseteq k((q))$ and of $k$-algebra homomorphisms $\theta_{\mathrm{fin}}\colon k\otimes_A\mathrm{chartAlgFin}\,A\,K\,j\to \mathrm{chartRing}\,k\,\{t\}$ and $\theta_{\infty}\colon k\otimes_A\mathrm{chartAlgInf}\,A\,K\,j\to \mathrm{chartRing}\,k\,\{t^{-1}\}$, the targets being the elements of the Igusa function field integral over $k[t]$, respectively over $k[t^{-1}]$, such that: the Laurent expansion of $t$ is $\mathrm{jqModC}\,k=q^{-1}\cdot\mathrm{jNum}(q)$ over $k$; $\theta_{\mathrm{fin}}(1\otimes j)=t^{p}$ and $\theta_{\infty}(1\otimes j^{-1})=(t^{-1})^{p}$; whenever $b$ in the finite chart algebra and $b'$ in the infinite one satisfy $b=b'j^{n}$ in $K$ one has $\theta_{\mathrm{fin}}(1\otimes b)=\theta_{\infty}(1\otimes b')\,t^{pn}$; for $b$ in either chart algebra and $x,y\in A[[q]]$ with $y$ of non-zero reduction and $\sigma(b)\cdot y=x$ in $L((q))$, the Laurent expansion of $\theta(1\otimes b)$ equals $\bar x/\bar y$ in $k((q))$, the reductions being taken along $A\to k$; and the kernels of $\theta_{\mathrm{fin}}$ and $\theta_{\infty}$ are generated as ideals by those pure tensors $1\otimes b$ that they kill. The chart algebras `chartAlgFin A ↥K j` and `chartAlgInf A ↥K j` are the subalgebras $\mathrm{chartAlg}\,A\,K\,\{j\}$ and $\mathrm{chartAlg}\,A\,K\,\{j^{-1}\}$ of the two-chart integral model attached to $j$ and $j^{-1}$.
--
--   This is the well-definedness half of the comparison, in characteristic $p$, between the two-chart integral model of the modular curve of level $\Gamma_1(M)\cap\Gamma_1(p)$ over the cyclotomic discrete valuation ring $A$ and the Igusa curve attached to the weight-one form $w$: reading the integral $j$-charts through the level-$p$ automorphism $\sigma$ and reducing $q$-expansions sends $j$ to the $p$-th power of the Igusa coordinate. It is used by the strengthening that adds surjectivity of the two maps, and by the statement producing a curve model over $k$ birational to the special fibre of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_of_algEquiv_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem ModularCurve.XOneP.exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_of_algEquiv_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (w : ModularCurve.IntegralWeightOneForm k M) [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσ1 : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσ2 : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
      σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσ3 : ∀ W₀ : ValuationSubring ↥K,
      (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
      W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
        (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)) :
    ∃ (t : ↥(ModularCurve.igusaFunctionFieldX1C k M w))
      (θFin : k ⊗[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →ₐ[k]
        ↥(AlgebraicCurve.CurveModel.chartRing k ({t} : Set ↥(ModularCurve.igusaFunctionFieldX1C k M w))))
      (θInf : k ⊗[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) →ₐ[k]
        ↥(AlgebraicCurve.CurveModel.chartRing k ({t⁻¹} : Set ↥(ModularCurve.igusaFunctionFieldX1C k M w)))),

      ((t : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) = ModularCurve.jqModC k ∧

      ((θFin ((1 : k) ⊗ₜ[A] AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j)) :
          ↥(ModularCurve.igusaFunctionFieldX1C k M w)) = t ^ p ∧
      ((θInf ((1 : k) ⊗ₜ[A] AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j)) :
          ↥(ModularCurve.igusaFunctionFieldX1C k M w)) = t⁻¹ ^ p ∧

      (∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
          (b' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) (n : ℕ),
        (b : ↥K) = (b' : ↥K) * j ^ n →
        ((θFin ((1 : k) ⊗ₜ[A] b)) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          ((θInf ((1 : k) ⊗ₜ[A] b')) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) * t ^ (p * n)) ∧

      (∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (IsLocalRing.residue A) ≠ 0 →
        (((σ (b : ↥K) : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (((θFin ((1 : k) ⊗ₜ[A] b)) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
          HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
            HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))) ∧

      (∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) (x y : PowerSeries A),
        y.map (IsLocalRing.residue A) ≠ 0 →
        (((σ (b : ↥K) : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (((θInf ((1 : k) ⊗ₜ[A] b)) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
          HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
            HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))) ∧

      RingHom.ker θFin.toRingHom = Ideal.span {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ θFin z = 0} ∧
      RingHom.ker θInf.toRingHom = Ideal.span {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ θInf z = 0} := by sorry
