-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower
-- name    : ModularCurve.FullLevel.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/a4177e25-3cab-5ebf-83f5-0c8ff24b8b03
-- title:
--   Level automorphisms act on the Tate point as relabelling
-- statement:
--   Fix a prime $q\ge 5$, a nonzero $M'$ with $q\nmid M'$, a prime $\ell\ge 3$ with $\ell\neq q$ and $\ell\nmid M'$, a field $L$ of characteristic $0$ and a primitive $(q\ell)$-th root of unity $\xi\in L$ admitting a ring homomorphism $\iota:L\to\mathbb C$ with $\iota\xi=e^{2\pi i/(q\ell)}$. Let $K$ be the intermediate field of $L\subset\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise images of the function field `xHFunctionField` of level $(q\ell)^2M'$ for the subgroup `levelH` $=\ker\big((\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times\big)$, let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, acting on $K$ compatibly, and let $j\in K$ be a nonzero element whose image in $\mathrm{LaurentSeries}\,L$ is the $q$-expansion `jq` of the $j$-function. Let $A_0$ be a commutative ring mapping to $L$, to $A$ and to $K$ compatibly, with $\ell$ and $M'$ units in $A_0$, together with: the two variable-change compatibilities `hℓ`, `hM` for Katz level-$\ell$ structures and for `IsGamma0PowAt` kernel polynomials; group laws $\mathcal G$ over $A_0$ that are chord–tangent and have the origin as identity; a level transport $\mathcal T$ for $\mathcal G$ at $q$ that is a section transport; the two hypotheses `hVC`, `hCO` providing graded ring homomorphisms on projective-model rings realising variable changes and coefficient changes (with the irrelevant-ideal condition); and a family $\rho$ of problem automorphisms of the level moduli datum of `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, indexed by $\Gamma_0(M')$, pinned by `hρ`: over any field that is an $A_0$-algebra, $\rho(\gamma)$ sends the class of a raw point $x$ with invertible discriminant to the class of any raw point with the same curve and the same $\Gamma_0(M')$-polynomials, whose level-$\ell$ data and Drinfeld pair are the $\bar\gamma$-relabellings of those of $x$. Then there is a $K$-point $x_0$ of the datum such that: its $j$-invariant, read in $\mathrm{LaurentSeries}\,L$, is `jqNModC L (q*ℓ)`; there are a variable change $C$ over $\mathrm{LaurentSeries}\,L$ and a raw point $r$ over $K$ with class $x_0$ such that $C.u\,(2x_\infty+\tfrac16)=2y_\infty+x_\infty$ for $(x_\infty,y_\infty)$ the Tate toric cusp point `cuspPoint L (q*ℓ) ξ ![1,0]`, $C.r=-\tfrac1{12}$, $C.s=-\tfrac12$, $C.t=\tfrac1{24}$; the curve of $r$ pushed to $\mathrm{LaurentSeries}\,L$ is $C\cdot$`tateBase L (q*ℓ)`; for each prime $p\mid M'$, each field $F'$ with a ring homomorphism $f:L\to F'$ and each primitive $p^{v_p(M')}$-th root of unity $\zeta\in F'$, the $p$-component of the $\Gamma_0$-level datum of $r$, transported to $\mathrm{LaurentSeries}\,F'$, is the $C$-variable change in degree `gamma0PowDeg p (v_p M')` of $\prod_a\big(X-\mathrm{toricPoint}\,F'\,(q\ell)\,(\zeta^a)_1\big)$ over $1\le a\le p^{v_p(M')}/2$ with $p\nmid a$; the level-$\ell$ datum of $r$ becomes the $C$-variable change of `cuspData L (q*ℓ) ξ ![q,0] ![0,-q]`; and the Drinfeld sections of $r$ pass through points of $K$ whose images are the four coordinates of the $C$-variable change of `cuspData L (q*ℓ) ξ ![ℓ,0] ![0,-ℓ]`. Moreover, for every $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lying in $\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ that is a level automorphism at $\gamma^{-1}$ in the sense of `IsLevelAutAt` for the data $(L,q\ell,\xi,q\ell,(q\ell)^2M',$`levelH`$)$, the functorial map of the datum along $\tau$ (as an $A_0$-algebra map) sends $x_0$ to $\rho(\gamma)$ applied to $x_0$.
--
--   This identifies, at the Tate curve over the full-level function field, the action of the level automorphisms of $K/L$ on the rigidified moduli problem with $\Gamma_0(M')$, Katz level-$\ell$ and Drinfeld level-$q$ data: it is the $A_0$-base form of the statement, obtained from the version over the discrete valuation ring $A$ by restriction of scalars. It feeds the auxiliary full-level results that classify level automorphisms and compute the induced action on completions and stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower
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

    (A₀ : Type) [CommRing A₀] [Algebra A₀ L] [Algebra A₀ ↥K] [IsScalarTower A₀ L ↥K]
    [Algebra A₀ A] [IsScalarTower A₀ A ↥K]

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)

    (hρ : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A₀ T]
      (x x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') :
    ∃ x₀ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K,
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) ∧

      (haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy)) ∧
      ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A₀) x₀ = (ρ ⟨γ, hγ⟩).act x₀ := by sorry
