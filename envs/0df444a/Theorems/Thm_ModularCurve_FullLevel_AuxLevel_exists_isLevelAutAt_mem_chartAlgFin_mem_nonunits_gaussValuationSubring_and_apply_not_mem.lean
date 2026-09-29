-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem
-- name    : ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/a7a20b46-c3b9-5154-94af-42fdb63bde02
-- title:
--   A level automorphism moving the Gauss prime of the finite chart
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'$ be a non-zero natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb Q$ of order $q\ell$, let $\zeta\in L$ be a primitive $q$-th root of unity and $\xi\in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb Q\to L$ of the function field $\mathtt{xHFunctionField}$ of level $(q\ell)^2M'$ attached to the subgroup $\mathtt{levelH}$, the kernel of the reduction $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$; let $\varpi$ generate the maximal ideal of $A$. Let $j\in K$, $j\neq 0$, be the element whose Laurent series is the image of the $q$-expansion $\mathtt{jq}=T^{-1}\cdot\mathtt{jNumQ}$ of the modular invariant. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x,y$ over $A$ with $y$ having non-zero reduction modulo the maximal ideal of $A$ and $f\cdot y=x$ in $\mathrm{LaurentSeries}\,L$ (the Gauss valuation ring). Then there exist $\gamma\in \mathrm{SL}_2(\mathbb Z)$ lying in both $\Gamma(\ell)$ and $\Gamma_0(M')$, an $L$-algebra automorphism $\tau$ of $K$ which is a level automorphism at $\gamma^{-1}$ in the sense of $\mathtt{IsLevelAutAt}$ — for every weight $k$, every pair of modular forms $f,g$ for $\Gamma_H((q\ell)^2M',\mathtt{levelH})$ with integral $q$-expansions $p_f,p_g$, $p_g$ having non-zero associated series, every $x\in K$ whose Laurent series is the image of $p_f/p_g$, and every ring embedding $\iota:L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, one has $\iota(\tau x)\cdot q\text{-exp}(g\mid_k \gamma') = q\text{-exp}(f\mid_k \gamma')$, where $\gamma'=\mathtt{conjElemN}\,(q\ell)\,\gamma^{-1}$ is the matrix $\begin{pmatrix} a & b/(q\ell)\\ (q\ell)c & d\end{pmatrix}$ — and an element $H\in K$ integral over $A[j]$ (that is, $H\in\mathtt{chartAlgFin}\,A\,K\,j$) such that $H$ is a non-unit of $W_0$ while $\tau H$ is not.
--
--   This is the statement that some automorphism of the modular function field coming from a level structure in $\Gamma(\ell)\cap\Gamma_0(M')$ moves the Gauss prime of the finite chart algebra $A[j]^{\mathrm{int}}$, the prime cut out on it by the maximal ideal of the Gauss valuation ring $W_0$. It is used in the construction of two distinct primes of the finite chart lying over a supersingular point of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem
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

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma ℓ) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (τ : ↥K ≃ₐ[L] ↥K) (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
      (H : ↥K), H ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ∧ H ∈ W₀.nonunits ∧ τ H ∉ W₀.nonunits := by sorry
