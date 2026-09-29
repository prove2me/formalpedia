-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow
-- name    : ModularCurve.FullLevel.map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/71cc25d3-fd76-5758-946d-a623255ce698
-- title:
--   A Γ₀(M') element fixing the Tate point is ± 1 mod qℓ
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, neither dividing the nonzero natural number $M'$. Let $L$ be a field of characteristic zero containing a primitive $q\ell$-th root of unity $\xi$ for which some ring homomorphism $\iota\colon L\to\mathbb{C}$ satisfies $\iota(\xi)=e^{2\pi i/(q\ell)}$, and let $K$ be the intermediate field of $L\subseteq L((X))$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$, where $H\le(\mathbb{Z}/(q\ell)^2M')^\times$ is the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal and $\ell$ and $M'$ invertible in $A$, and let $K$ be an $A$-algebra compatibly with $A\to L\to K$; let $j\in K$ be the element whose Laurent expansion is the coefficientwise image of the $q$-expansion of the modular $j$-function, assumed nonzero. Assume: level-$\ell$ data and the $\Gamma_0$-type kernel polynomials transform correctly under Weierstrass variable changes (`hℓ`, `hM`, the latter via `kernelVariableChangeDeg`); $\mathcal{G}$ is a family of relative group laws on the projective models of curves with unit discriminant over $A$-algebras, chord–tangent realisable and with the origin as identity; $\mathcal{T}$ is a level transport for $\mathcal{G}$ and $q$ satisfying `IsSectionTransport`; and variable changes and coefficient maps are realised by graded homomorphisms of the projective model rings dominating the irrelevant ideals (`hVC`, `hCO`). Points of the moduli datum attached to `rigidDataPow A ℓ M' q` over an $A$-algebra $T$ are Weierstrass curves over $T$ with unit discriminant equipped with, for each prime $p\mid M'$, a polynomial satisfying `IsGamma0PowAt` for $p^{v_p(M')}$, a level-$\ell$ structure (a `LevelPData` satisfying `IsLevelPStructure`), and a raw Drinfeld pair which is a Drinfeld $q$-basis, taken modulo variable change; `jOf` is the $j$-invariant. Let $x$ be such a point over $K$ whose $j$-invariant has Laurent expansion $j(q^{q\ell})$, and let $\rho$ assign to each $\gamma\in\Gamma_0(M')$ an automorphism of this moduli problem, subject to the requirement that over any field $T$ which is an $A$-algebra, if raw data $x'$ has the same curve and the same $\Gamma_0$-component as $x$, its level-$\ell$ data is `LevelPData.relabel` of that of $x$ by the integral matrix $\gamma$, and its Drinfeld pair is `RawDrinfeldPair.relabel` of that of $x$ by $\gamma$, then $\rho(\gamma)$ carries the class of $x$ to the class of $x'$. Then for any $\gamma\in\Gamma_0(M')$ with $\rho(\gamma)\cdot x=x$, the image of $\gamma$ in $\mathrm{SL}_2(\mathbb{Z}/q\ell)$ is $1$ or $-1$.
--
--   This is the rigidity step for the diamond action on the rigidified full-level moduli problem at the Tate point: an element of $\Gamma_0(M')$ whose relabelling of the level data fixes the point with $j=j(q^{q\ell})$ can only act through $\pm 1$ on the $q\ell$-torsion, because the $j$-invariant in question is neither $0$ nor $1728$, so the only automorphisms of the underlying curve are $\pm 1$. It is used in the identification of the level automorphism group, feeding [`ModularCurve.FullLevel.AuxLevel.map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom`](thm.html#ModularCurve.FullLevel.AuxLevel.map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom) and [`ModularCurve.FullLevel.levelAut_eq_one_of_forall_apply_classify_eq_gamma0Pow_tatePoint`](thm.html#ModularCurve.FullLevel.levelAut_eq_one_of_forall_apply_classify_eq_gamma0Pow_tatePoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow
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
        IsCoefficientHom W f.toRingHom φ)
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)

    (hρ : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A T]
      (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x')
    (γ : ↥(CongruenceSubgroup.Gamma0 M')) (hfix : (ρ γ).act x = x) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) (γ : SL(2, ℤ)) = 1 ∨
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) (γ : SL(2, ℤ)) = -1 := by sorry
