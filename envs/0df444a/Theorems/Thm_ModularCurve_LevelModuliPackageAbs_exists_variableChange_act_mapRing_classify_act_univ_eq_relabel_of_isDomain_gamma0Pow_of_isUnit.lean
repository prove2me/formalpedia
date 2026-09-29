-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_of_isDomain_gamma0Pow_of_isUnit
-- name    : ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_of_isDomain_gamma0Pow_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/463b629d-1542-5c78-8032-63590f946222
-- title:
--   Relabelling automorphism pulls back to γ-relabelled datum over a domain
-- statement:
--   Fix a prime $q$, a prime $\ell\ge 3$, a nonzero natural number $M'$, and a commutative ring $A_0$ in which $\ell$ is invertible; assume the two functoriality hypotheses that a Katz level-$\ell$ datum for $W$ stays one for $C\bullet W$ after the coordinate substitution `LevelPData.variableChange C`, and that the predicate `IsGamma0PowAt` is preserved by `kernelVariableChangeDeg`. Let $\mathcal G$ be a family of group laws on the projective Weierstrass models over $A_0$-algebras, chord–tangent and with the origin as identity, and $\mathcal T$ a level transport for Drinfeld $\Gamma(q)$-structures with the section-transport property. These assemble, via `rigidDataPow`, into rigid Weierstrass data whose raw objects over an $A_0$-algebra $T$ are: a Weierstrass curve with unit discriminant, a family of polynomials indexed by the prime factors of $M'$ satisfying `IsGamma0PowAt` at the corresponding exponent, a level-$\ell$ quadruple $(x_P,y_P,x_Q,y_Q)$ which is a Katz level-$\ell$ structure, and a raw Drinfeld pair $(P,Q)$ which is a Drinfeld $\Gamma(q)$-basis; points are raw objects modulo variable change. Let $P_0$ be a fine moduli package for the associated moduli datum: a ring $B_0$ with a universal point `univ` such that every point over $T$ is the image of `univ` under a unique $A_0$-algebra map, and let $x$ be a raw object over $B_0$ whose class is `univ`. Let $R$ be an $A_0$-algebra which is a domain, $\iota : B_0 \to R$ an $A_0$-algebra map, $\gamma\in\mathrm{SL}_2(\mathbb Z)$, and $\rho_\gamma$ an automorphism of the moduli problem (a natural, $j$-preserving self-map of the point functor). Assume the pinning hypothesis: for every field $T$ that is an $A_0$-algebra and raw objects $y,y'$ over $T$ with $y$'s Drinfeld curve having unit discriminant, if $y'$ has the same curve and the same $\Gamma_0$-slot as $y$, its level-$\ell$ quadruple is `LevelPData.relabel` of $y$'s by $\gamma$, and its Drinfeld pair is `RawDrinfeldPair.relabel` of $y$'s by $\gamma$ (the two $\mathbb Z$-linear combinations $\gamma_{00}P+\gamma_{10}Q$, $\gamma_{01}P+\gamma_{11}Q$ formed with $\mathcal G$), then $\rho_\gamma$ sends the class of $y$ to the class of $y'$. Writing $x_R$ for the base change of $x$ along $\iota$, the conclusion asserts: the Drinfeld curve of $x_R$ has unit discriminant, and there are a variable change $V$ over $R$ and a raw object $x'$ over $R$ such that $V$ applied to the base change of $x$ along $\iota\circ P_0.\mathrm{classify}(\rho_\gamma\cdot\mathrm{univ})$ equals $x'$, with $x'$ having the same curve and the same $\Gamma_0$-slot as $x_R$, Drinfeld pair the $\gamma$-relabelling of that of $x_R$, and level-$\ell$ quadruple whose image in $\mathrm{Frac}\,R$ is the $\gamma$-relabelling of the image of that of $x_R$.
--
--   This is the comparison, over a domain, between pulling the universal rigid datum back along the classifying map of a relabelling automorphism of the moduli problem and relabelling the datum itself by $\gamma\in\mathrm{SL}_2(\mathbb Z)$: the two agree up to a Weierstrass variable change, with the level-$\ell$ slot compared only after passing to the fraction field. It is used in the analysis of the induced ring automorphism of $B_0$ and of its effect on the origin parameter for the $\Gamma_0(M')\cap\Gamma(\ell)\cap\Gamma_{\mathrm{Dr}}(q)$ moduli ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_of_isDomain_gamma0Pow_of_isUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_of_isDomain_gamma0Pow_of_isUnit
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓA : IsUnit ((ℓ : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsDomain R] [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)

    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (ργ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [Algebra A₀ T]
        (y y' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y') :
    let xR := (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x
    ∃ (hΔ : IsUnit xR.level.2.2.curve.Δ) (V : WeierstrassCurve.VariableChange R) (x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw R),
      (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act V ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (ι.comp (P₀.classify (ργ.act P₀.univ))) x) = x' ∧
      x'.curve = xR.curve ∧ x'.level.1 = xR.level.1 ∧
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) xR.level.2.2 hΔ ∧

      x'.level.2.1.map (algebraMap R (FractionRing R)) =
        ModularCurve.LevelRelabelling.LevelPData.relabel (xR.curve.map (algebraMap R (FractionRing R)))
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
          (xR.level.2.1.map (algebraMap R (FractionRing R))) := by sorry
