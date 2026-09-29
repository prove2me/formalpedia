-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/9f1998dd-154c-5a2f-828d-627a1210f704
-- title:
--   Tate raw datum: weight-one twist, cusp levels, j=j(mathsf q^{qℓ})
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\ne q$, a nonzero natural number $M'$ divisible by neither $q$ nor $\ell$, a field $L$ of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$ for which some ring homomorphism $L\to\mathbb C$ sends $\xi$ to $e^{2\pi i/(q\ell)}$, and let $K\subseteq L(\!(\mathsf q)\!)$ be the intermediate field $\mathrm{laurentBaseChange}$ of the $\Gamma_H$-function field [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79), i.e. the subfield generated over $L$ by the coefficientwise image of that field of $q$-expansions, where `levelH` is the kernel of reduction $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\ell$, $M'$ units, acting on $K$ compatibly, and let $j\in K$ have image the $q$-expansion $\mathrm{coeffEmb}_L(\mathsf{jq})$ and be nonzero. Assume: level-$\ell$ Katz structures and $\Gamma_0(p^k)$-kernel polynomials transform under variable change as in `IsLevelPStructure`/`IsGamma0PowAt` (hypotheses `hℓ`, `hM`); group laws $\mathcal G$ over $A$ that are chord–tangent and have the origin as identity; a level transport $\mathcal T$ for $(\mathcal G,q)$ satisfying `IsSectionTransport`; and graded ring homomorphisms on the projective-model graded rings realising variable changes (`hVC`) and coefficient changes (`hCO`), each dominating the irrelevant ideal. Then there are a variable change $C$ over $L(\!(\mathsf q)\!)$ and a raw datum $x$ over $K$ for `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` (a Weierstrass curve with unit discriminant together with a $\Gamma_0$-tuple, level-$\ell$ data and a Drinfeld pair satisfying the respective level conditions) such that: (i) writing $(x_0,y_0)=\mathrm{cuspPoint}_L(q\ell,\xi,(1,0))$ for the toric point at $\xi$, one has $u\,(2x_0+\tfrac16)=2y_0+x_0$, $r=-\tfrac1{12}$, $s=-\tfrac12$, $t=\tfrac1{24}$; (ii) the curve of $x$, pushed to $L(\!(\mathsf q)\!)$, is $C\bullet\mathrm{tateBase}_L(q\ell)$; (iii) for every prime $p\mid M'$, with $k=v_p(M')$, every field $F'$, ring homomorphism $f:L\to F'$ and primitive $p^k$-th root of unity $\zeta\in F'$, the $p$-component of the $\Gamma_0$-tuple, pushed to $L(\!(\mathsf q)\!)$ and then mapped by $f$ coefficientwise, equals $\mathrm{kernelVariableChangeDeg}$ of $C$ (in degree $\mathrm{gamma0PowDeg}\,p\,k$) applied to $\prod_{1\le a\le p^k/2,\;p\nmid a}(X-(\mathrm{toricPoint}_{F'}(q\ell,\zeta^a))_1)$; (iv) the level-$\ell$ data of $x$ becomes $(\mathrm{cuspData}_L(q\ell,\xi,(q,0),(0,-q)))$ transformed by $C$; (v) there are $P_x,P_y,Q_x,Q_y\in K$ whose images are the four coordinates of $(\mathrm{cuspData}_L(q\ell,\xi,(\ell,0),(0,-\ell)))$ transformed by $C$, and the two sections of the Drinfeld pair of $x$ pass through $(P_x,P_y)$ and $(Q_x,Q_y)$; (vi) the $j$-invariant attached by `toLevelModuliDatum.jOf` to the class of $x$ has image $\mathrm{jqNModC}_L(q\ell)$, the $q$-expansion of $j$ in $\mathsf q^{q\ell}$.
--
--   This is the construction of the Tate point of the full-level moduli problem of level $(q\ell)^2M'$: a raw rigid Weierstrass datum over the base-changed $\Gamma_H$-function field whose curve is a weight-one twist of the Tate curve, whose level-$\ell$ and Drinfeld data are the cusp data at the indicated torsion indices, and whose $\Gamma_0$-tuple consists of the generator kernels of $\mu_{p^k}$. It is used by the theorems producing a point of the moduli problem compatible with the level automorphisms and the algebra homomorphisms out of the level-moduli package at the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow.lean

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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L))
      (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K),

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ) := by sorry
