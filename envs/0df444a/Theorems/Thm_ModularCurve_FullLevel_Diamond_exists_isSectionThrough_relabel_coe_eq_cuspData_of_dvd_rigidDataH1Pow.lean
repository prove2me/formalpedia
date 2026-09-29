-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/8d0c35d5-d253-518b-ad6a-2fdbbae3bb90
-- title:
--   Relabelled Drinfeld pair at the Tate point, level H₁
-- statement:
--   Fix a prime $q$, a natural number $M' \neq 0$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $L$ be a field of characteristic zero, $\xi \in L$ a primitive $(q\ell_g)$-th root of unity admitting a ring homomorphism $L \to \mathbb{C}$ carrying $\xi$ to $\exp(2\pi i/(q\ell_g))$, and let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell_g)^\times$. Let $K$ be the intermediate field of $\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image, under coefficientwise extension along $\mathbb{Q} \to L$, of the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79), and let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\ell_g$ and $M'$ invertible in $A$, and acting on $K$ compatibly; let $j \in K$ be the element whose Laurent expansion is that of the $j$-function, assumed nonzero. Assume: the three variable-change equivariance hypotheses for $\Gamma_1(\ell_g)$-point data, for $\Gamma_0(p^k)$ kernel polynomials under [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104), and for divisibility of [`ModularCurve.inLineMulPoly`](def/ModularCurve_WeierstrassH1Pow.html#L18); group laws $\mathcal{G}$ over $A$ that are chord–tangent and have the origin as identity; a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ that is a section transport; and the two hypotheses providing graded ring homomorphisms of projective models realising variable changes and coefficient changes (with the irrelevant-ideal condition). Let $C_0$ be a variable change over $\mathrm{LaurentSeries}\,L$ and let $x$ be a raw point over $K$ of the rigid moduli datum `rigidDataH1Pow A ℓg M' q …`, that is, a Weierstrass curve over $K$ with unit discriminant together with a family of $\Gamma_0(p^{v_p(M')})$ kernel polynomials, a $\Gamma_1(\ell_g)$ level datum, and a raw Drinfeld pair, satisfying the corresponding level conditions and the $\Gamma_1$-link divisibility. Assume that the base change of $x$'s curve to $\mathrm{LaurentSeries}\,L$ equals $C_0 \bullet \mathrm{tateBase}\,L\,q$, and that there are $P_x,P_y,Q_x,Q_y \in K$ whose Laurent expansions are the four coordinates of the level-$q$ cusp datum at index vectors $(1,0)$ and $(0,-1)$ for the root of unity $\xi^{\ell_g}$, twisted by $C_0$, the Drinfeld sections $P$ and $Q$ of $x$ passing through $(P_x,P_y)$ and $(Q_x,Q_y)$ in the sense of `IsSectionThrough` (factorisation through the $z$-chart with these affine coordinates). Finally let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ with $q \mid \gamma_{00}$, and let $h_\Delta$ witness that the discriminant of the Drinfeld pair's curve is a unit. Then there are $a,b,a',b' \in K$ such that the relabelled pair $\mathcal{G}$-$\gamma$-combination `RawDrinfeldPair.relabel`, whose first section is $\gamma_{00}P + \gamma_{10}Q$ and whose second is $\gamma_{01}P + \gamma_{11}Q$, has its first section passing through $(a,b)$ and its second through $(a',b')$, and moreover $a$ and $b$ have Laurent expansions equal to the $x$- and $y$-coordinates of the first cusp point of the level-$q$ cusp datum for $\xi^{\ell_g}$ at index vectors $(0,-\gamma_{10})$ and $(\gamma_{01},-\gamma_{11})$ in $\mathbb{Z}/q$, twisted by $C_0$.
--
--   This computes the effect on the Drinfeld basis of relabelling by a matrix of $\Gamma_0(M')$ with $q \mid \gamma_{00}$, at the representative of the $\Gamma_0(M') \times \Gamma_1(\ell_g) \times \Gamma(q)$ moduli problem pinned to the Tate curve, identifying the first relabelled section with the explicit level-$q$ cusp point of index $(0,-\gamma_{10})$ while the second is only asserted to pass through some affine point. It is the $H_1$-level form of the relabelling step used in the analysis of the cusps and of the diamond action on the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule

theorem ModularCurve.FullLevel.Diamond.exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K)

    (hxc : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q)

    (hxD : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy)

    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (hγq : (q : ℤ) ∣ (γ 0 0 : ℤ))
    (hΔ : IsUnit x.level.2.2.curve.Δ) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ a b a' b' : ↥K,
      IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ).P a b ∧
      IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ).Q a' b' ∧
      (a : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg)
        ![0, -(((γ 1 0 : ℤ) : ZMod q))] ![((γ 0 1 : ℤ) : ZMod q), -(((γ 1 1 : ℤ) : ZMod q))]).variableChange C₀).xP ∧
      (b : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg)
        ![0, -(((γ 1 0 : ℤ) : ZMod q))] ![((γ 0 1 : ℤ) : ZMod q), -(((γ 1 1 : ℤ) : ZMod q))]).variableChange C₀).yP := by sorry
