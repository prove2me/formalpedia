-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/59ff14ca-27c2-59ad-950c-cc5d338f1ff6
-- title:
--   A level automorphism moving the Gauss prime
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^{\times}$ with the kernel of reduction to $(\mathbb{Z}/\ell)^{\times}$, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ (the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ cut out by $H_1$). Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\zeta$ in the image of $A \to L$, let $K$ be an $A$-algebra compatibly with $L$, let $j \in K$ be the element whose Laurent series is the coefficientwise image of the $q$-expansion $\mathsf{q}^{-1}\cdot(\text{integral } j\text{-numerator})$ of the modular $j$-function, with $j \ne 0$, and let $\varpi$ generate the maximal ideal of $A$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$ after pushing $x, y$ forward to $L$ (the Gauss valuation ring). Then there exist $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in both $\Gamma(\ell)$ and $\Gamma_0(M')$, an $L$-algebra automorphism $\tau$ of $K$ which is a level automorphism at $\gamma^{-1}$ in the sense that for every weight $k$, all modular forms $f, g$ of weight $k$ on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f, p_g$ and with the Laurent series attached to $p_g$ nonzero, every $x \in K$ whose Laurent series is the image of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, one has $\iota_*(\tau x) \cdot (g \mid_k \gamma^{-1}_{(q)})^{\wedge} = (f \mid_k \gamma^{-1}_{(q)})^{\wedge}$ on $q$-expansions, where $\gamma^{-1}_{(q)}$ denotes the conjugate matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ of $\gamma^{-1} = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, and an element $H \in K$ integral over $A[j]$ such that $H$ lies in the maximal ideal of $W_0$ while $\tau H$ does not.
--
--   This is the auxiliary-level ($q \in \{2,3\}$, guard prime $\ell \equiv 11 \pmod{12}$) form of the statement that the Gauss point of the two-chart integral model is not fixed by the level automorphisms coming from $\Gamma(\ell) \cap \Gamma_0(M')$: some element of the chart algebra $A[j]^{\mathrm{int}}$ vanishes at the Gauss prime but not at its image under $\tau$. It feeds the statement that at least two primes of the chart algebra lie over the relevant point of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem_of_isPrimitiveRoot_mul_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_mem_chartAlgFin_mem_nonunits_gaussValuationSubring_and_apply_not_mem_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
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
      (τ : ↥K ≃ₐ[L] ↥K) (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
      (H : ↥K), H ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ∧ H ∈ W₀.nonunits ∧ τ H ∉ W₀.nonunits := by sorry
