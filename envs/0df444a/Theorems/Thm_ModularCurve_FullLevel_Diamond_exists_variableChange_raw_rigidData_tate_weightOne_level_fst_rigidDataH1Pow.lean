-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/51a747a4-302e-5c41-9e68-2ee93f26c1b0
-- title:
--   Tate point of the H₁ moduli problem over K
-- statement:
--   Let $q$ be a prime, $M'\neq 0$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $q\ell_g$-th root of unity admitting a ring homomorphism $\iota:L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/(q\ell_g)}$, and let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernels of reduction to $(\mathbb Z/q)^\times$ and to $(\mathbb Z/\ell_g)^\times$. Let $K\subset L((\mathsf q))$ be the field generated over $L$ by the image, under coefficientwise extension $\mathbb Q\to L$, of the $q$-expansion function field of level $H_1$ and $q^2M'$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, acting on $K$ compatibly, and let $j\in K$ be the element whose Laurent expansion is the $q$-expansion of the $j$-function, assumed nonzero; $\ell_g$ and $M'$ are units in $A$. Assume further the variable-change compatibilities for $\Gamma_1(\ell_g)$-points, for $\Gamma_0(p^k)$-kernel polynomials and for divisibility of the in-line multiplication polynomials (the hypotheses `hℓ`, `hM`, `hL` entering `rigidDataH1Pow`), group laws $\mathcal G$ over $A$ that are chord–tangent and have the origin as identity, a level transport $\mathcal T$ for $\mathcal G$ at $q$ that is a section transport, and the existence, over every $A$-algebra, of graded ring homomorphisms on projective-model graded rings realising variable changes and coefficient maps and dominating the irrelevant ideal. Then there are a variable change $C$ over $L((\mathsf q))$ and a raw datum $x$ for `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯` over $K$ — that is, a Weierstrass curve over $K$ with unit discriminant together with: kernel polynomials $h_p$ for the prime factors $p\mid M'$ satisfying `IsGamma0PowAt` at $(p,v_p(M'))$, a `LevelPData` which is a $\Gamma_1(\ell_g)$-point (the two listed points coinciding, lying on the curve, with $\mathrm{pre}\Psi_{\ell_g}$ vanishing at its abscissa), a Drinfeld pair at $q$ satisfying the level condition, and the link condition that $h_{\ell_g}$ divides the in-line multiplication polynomial $\mathrm{inLineMulPoly}$ at $\ell_g$, $\ell_g^{v_{\ell_g}(M')-1}$ and the abscissa of the $\Gamma_1$-point — such that: (i) $C$ has $r=-1/12$, $s=-1/2$, $t=1/24$ (constant Laurent series) and $u$ normalised by $u\,(2x(P)+1/6)=2y(P)+x(P)$, where $P=\mathrm{tateToricPoint}$ at $\xi^q$ for the Tate curve in $\mathsf q^{\,q}$; (ii) the curve of $x$, pushed to $L((\mathsf q))$, equals $C\cdot\mathrm{tateBase}$; (iii) for each prime $p\mid M'$, each field $F'$, each $f:L\to F'$ and each primitive $p^{v_p(M')}$-th root of unity $\zeta\in F'$, the image of $h_p$ in $F'((\mathsf q))$ equals the degree-$\mathrm{gamma0PowDeg}(p,v_p(M'))$ variable-change transform under $f(C)$ of $\prod_{1\le a\le p^{v_p(M')}/2,\ p\nmid a}\bigl(X-x(\mathrm{toricPoint}(\zeta^a))\bigr)$; (iv) the $\Gamma_1$-slot of $x$ maps to the $C$-transform of the level datum both of whose points are $P$; (v) there are $P_x,P_y,Q_x,Q_y\in K$ whose Laurent expansions are the four coordinates of the $C$-transform of $\mathrm{cuspData}$ at $\xi^{\ell_g}$ for the vectors $(1,0)$ and $(0,-1)$, and the two Drinfeld sections of $x$ pass through $(P_x,P_y)$ and $(Q_x,Q_y)$; and (vi) the $j$-invariant attached to the class of $x$ has Laurent expansion $\mathrm{jqNModC}$, the $q$-expansion of $j$ in $\mathsf q^{\,q}$.
--
--   This produces the Tate point of the $H_1$-moduli problem ($\Gamma_0(M')\cap\Gamma_1(\ell_g)$ together with a Drinfeld $\Gamma(q)$-basis) as a raw rigid datum defined over the $q$-expansion function field $K$, pinned by an explicit variable change and with its $j$-invariant identified. It is the input to the identification of the level automorphisms of the moduli problem at the Tate point, and to the construction of the specialising $L((\mathsf q))$-algebra homomorphisms at minimal primes of the associated level moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow.lean

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

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow
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
        IsCoefficientHom W f.toRingHom φ) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L))
      (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K),

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L q ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) =
        (⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L q := by sorry
