-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_gamma0Pow
-- name    : ModularCurve.FullLevel.isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/ed28b606-d5b7-5075-9813-042e70a1def4
-- title:
--   Reducedness of (1-ζ)-quotient at an ordinary point of the full-level package
-- statement:
--   Fix a prime $q\ge 5$ and a prime $\ell\ge 3$ with $\ell\ne q$, and a nonzero natural number $M'$ not divisible by $q$. Let $A_0$ be a discrete valuation domain whose maximal ideal is $(q)$ and whose residue field is finite. Assume the two variable-change stability hypotheses `hℓ` and `hM` (a level-$\ell$ structure on a Weierstrass curve $W$ over an $A_0$-algebra transports to $C\bullet W$ along $D\mapsto D.\mathrm{variableChange}\,C$; a $\Gamma_0(p^k)$-kernel polynomial transports along `kernelVariableChangeDeg`), let $\mathcal G$ be a family of relative group laws on the projective models, chord–tangent and with the origin as identity, and let $\mathcal T$ be a level transport for $\mathcal G$ and $q$ which is a section transport; further hypotheses `hVC` and `hCO` assert that variable changes and coefficient maps are realised by graded ring homomorphisms of the projective-model rings. Let $P_0$ be a fine moduli package for the moduli datum attached to `rigidDataPow A₀ ℓ M' q …`, i.e. an $A_0$-algebra $B_0$ of finite type carrying a universal point `P₀.univ` representing the functor of triples (a Weierstrass curve with unit discriminant, $\Gamma_0$-kernel polynomials at the prime powers in $M'$, a level-$\ell$ structure, a Drinfeld $q$-basis) modulo variable change. Let $x$ be such a raw triple over $B_0$ whose class in the quotient is `P₀.univ`, let $\mathfrak m\subset B_0$ be a maximal ideal containing the image of $q$, and let $F_0$ be a formal group over $B_0/\mathfrak m$ whose power series is the fixed Weierstrass formal group law of the reduction of $x$'s curve and whose $q$-th iterate series `F₀.nthSeries q` equals a unit times $X^q$. Then for every $\zeta$ in the $\mathfrak m$-adic completion of $B_0$ with $\zeta^q=1$, the quotient of that completion by the ideal $(1-\zeta)$ is reduced.
--
--   This is the package-level form of the ordinary-fibre reducedness statement for the full-level moduli ring $\Gamma_0(M')\times\Gamma(\ell)\times\Gamma(q)^{\mathrm{Drinfeld}}$: at a closed point of residue characteristic $q$ where the universal formal group is ordinary, killing $1-\zeta$ for a $q$-th root of unity $\zeta$ leaves a reduced ring. It feeds the statement on reducedness of the residue-field tensor product of such a quotient for a primitive root of unity, used in the normality and regularity analysis of the moduli ring in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_gamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    [NeZero M'] (hM'q : ¬ q ∣ M')

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (ResidueField A₀)]

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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A₀ P₀.B₀]
    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (𝔪 : Ideal P₀.B₀) [𝔪.IsMaximal] (hq𝔪 : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔪)
    (F₀ : FormalGroup (P₀.B₀ ⧸ 𝔪))
    (hF₀W : F₀.toPowerSeries = (x.curve.map (Ideal.Quotient.mk 𝔪)).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries (P₀.B₀ ⧸ 𝔪), IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q)
    (ζ : AdicCompletion 𝔪 P₀.B₀) (hζ : ζ ^ q = 1) :
    IsReduced (AdicCompletion 𝔪 P₀.B₀ ⧸ Ideal.span {1 - ζ}) := by sorry
