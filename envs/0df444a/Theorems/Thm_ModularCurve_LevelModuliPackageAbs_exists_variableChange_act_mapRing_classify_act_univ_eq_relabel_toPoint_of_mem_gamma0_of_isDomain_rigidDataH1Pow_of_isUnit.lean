-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
-- name    : ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0a8e769d-5905-5fd4-a22c-694ba3c2b7f6
-- title:
--   Relabelling automorphism pulls back by a variable change
-- statement:
--   Fix a prime $q$, a nonzero $M' \in \mathbb{N}$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$; let $A_0$ be a commutative ring in which the image of $\ell_g$ is a unit. Assume the three transport hypotheses: variable changes preserve `IsGamma1Point` at $\ell_g$, preserve `IsGamma0PowAt` after applying `kernelVariableChangeDeg`, and carry divisibility of `inLineMulPoly` along. Let $\mathcal{G}$ be a family of relative group laws on the projective Weierstrass models over $A_0$-algebras which is chord–tangent and has the origin as identity, and $\mathcal{T}$ a level transport of raw Drinfeld pairs at $q$ satisfying `IsSectionTransport`; write $\mathcal{R}$ for the rigid Weierstrass datum `rigidDataH1Pow` built from these, whose raw points over $T$ consist of a Weierstrass curve with unit discriminant together with a family of $\Gamma_0(p^{k})$-kernel polynomials indexed by the prime factors of $M'$, a `LevelPData` quadruple $(x_P,y_P,x_Q,y_Q)$ which is a $\Gamma_1(\ell_g)$-point, and a Drinfeld $\Gamma(q)$-pair, linked by the `IsGamma1Link` divisibility. Let $P_0 = (B_0, \mathrm{univ})$ be a fine moduli package for the associated moduli datum, $x$ a raw point over $B_0$ whose class is $\mathrm{univ}$, $R$ a domain that is an $A_0$-algebra, $\iota : B_0 \to R$ an $A_0$-algebra map, $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $\gamma \in \Gamma_0(M')$, and $\rho_\gamma$ an automorphism of the moduli problem. The hypothesis on $\rho_\gamma$ (the pin) is: for every field $T$ that is an $A_0$-algebra and all raw points $y, y'$ over $T$ with the discriminant of the projective curve of $y$'s Drinfeld slot a unit, if $y'$ and $y$ have the same curve and the same $\Gamma_0$-slot, if the affine point of $y'$ (via `toPoint` on the base change of $y$'s curve) is $\gamma_{00}$ times that of $y$, if $y'$ has $x_Q = x_P$ and $y_Q = y_P$, and if the Drinfeld pair of $y'$ is the $\mathcal{G}$-relabelling $(P,Q) \mapsto (\gamma_{00}P + \gamma_{10}Q,\ \gamma_{01}P + \gamma_{11}Q)$ of that of $y$, then $\rho_\gamma$ sends the class of $y$ to the class of $y'$. Setting $x_R$ to be the base change of $x$ along $\iota$, the conclusion asserts the existence of a proof $h_\Delta$ that the discriminant of the projective curve in the Drinfeld slot of $x_R$ is a unit, of a variable change $V$ over $R$, and of a raw point $x'$ over $R$ such that $V$ applied to the base change of $x$ along $\iota$ composed after $P_0.\mathrm{classify}(\rho_\gamma \cdot \mathrm{univ})$ equals $x'$; $x'$ and $x_R$ have the same curve and the same $\Gamma_0$-slot; the Drinfeld pair of $x'$ is the $\mathcal{G}$-relabelling of that of $x_R$ by $\gamma$ (using $h_\Delta$); over $\mathrm{Frac}(R)$ the point `toPoint` of $x'$ on the base change of $x_R$'s curve equals $\gamma_{00}$ times the corresponding point of $x_R$; and $x'$ satisfies $x_Q = x_P$, $y_Q = y_P$.
--
--   This is the comparison, at the level of the representing ring, between an automorphism of the moduli problem that acts on field-valued points by $\gamma$-relabelling of the $\Gamma_1(\ell_g)$ and Drinfeld $\Gamma(q)$ slots and the pullback of the universal curve by an explicit Weierstrass variable change; the congruence $\ell_g \mid M'$ together with $\gamma \in \Gamma_0(M')$ makes $\gamma_{00}$ invertible modulo $\ell_g$, so that the diamond image of a $\Gamma_1(\ell_g)$-point is again such a point. It feeds the identification of the induced algebra automorphism of the representing ring and the computation of the linear part of the resulting origin parametrisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] SubalgebraClass.toAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A₀ : Type) [CommRing A₀]

    (hℓA : IsUnit ((ℓg : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsDomain R] [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)

    [DecidableEq (FractionRing R)]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (ργ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
        (y y' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y'.level.2.1.xP y'.level.2.1.yP =
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y.level.2.1.xP y.level.2.1.yP →
        y'.level.2.1.xQ = y'.level.2.1.xP → y'.level.2.1.yQ = y'.level.2.1.yP →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y') :
    let xR := (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x
    ∃ (hΔ : IsUnit xR.level.2.2.curve.Δ) (V : WeierstrassCurve.VariableChange R) (x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw R),
      (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).act V ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (ι.comp (P₀.classify (ργ.act P₀.univ))) x) = x' ∧
      x'.curve = xR.curve ∧ x'.level.1 = xR.level.1 ∧
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) xR.level.2.2 hΔ ∧

      (ModularCurve.LevelRelabelling.toPoint ((xR.curve).baseChange (FractionRing R))
          (algebraMap R (FractionRing R) x'.level.2.1.xP) (algebraMap R (FractionRing R) x'.level.2.1.yP) =
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
          ModularCurve.LevelRelabelling.toPoint ((xR.curve).baseChange (FractionRing R))
            (algebraMap R (FractionRing R) xR.level.2.1.xP) (algebraMap R (FractionRing R) xR.level.2.1.yP)) ∧
      x'.level.2.1.xQ = x'.level.2.1.xP ∧ x'.level.2.1.yQ = x'.level.2.1.yP := by sorry
