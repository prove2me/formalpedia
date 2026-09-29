-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
-- name    : ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/bfeb919f-691f-5ef2-a9c5-7c7e47c221cc
-- title:
--   Drinfeld-slot relabelling by g is a problem automorphism
-- statement:
--   Fix natural numbers $q,\ell,M'$ with $2\le q$ and a commutative ring $A$. Assume: $h\ell$, that for every $A$-algebra $T$, every Weierstrass curve $W/T$, every variable change $C$ and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ of elements of $T$, if $D$ is a level-$\ell$ structure on $W$ (both points satisfy the affine equation, both $x$-coordinates are roots of $\mathrm{preΨ}_\ell$, and the two independence elements $\mathrm{indepElt}$ are units) then the transported quadruple `D.variableChange C` is one on $C\bullet W$; $hM$, the analogous compatibility of `IsGamma0PowAt W p k h` with `kernelVariableChangeDeg`; a family $\mathcal G$ of relative group laws on the projective models of curves with unit discriminant, which is chord–tangent ($h\mathcal G$) and has the origin as identity ($h\mathcal G O$); a level transport $\mathcal T$ for $\mathcal G$ at $q$ satisfying the section-transport pin $h\mathcal T$; and existence of graded ring homomorphisms realising variable changes ($hVC$) and coefficient maps ($hCO$) on the projective-model gradings. Let $g\in M_2(\mathbb Z)$ have $\det g$ a unit in $\mathbb Z/q$. Then the level moduli datum attached to `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯`, whose raw data over an $A$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with a triple (a $\Gamma_0$ prime-power kernel polynomial for each prime factor of $M'$, a level-$\ell$ quadruple, a raw Drinfeld pair) satisfying the respective level conditions, admits a problem automorphism $\rho$, that is, a family of self-maps of the point sets $\mathrm{Pt}\,T$ commuting with base change along $A$-algebra maps and preserving the $j$-invariant, with the following property: for every $A$-algebra $T$, every raw datum $x$ over $T$, and every proof $h\Delta$ that the discriminant of the projective curve carried by the Drinfeld slot of $x$ is a unit, there is a raw datum $x'$ over $T$ having the same curve, the same $\Gamma_0(M')$ slot and the same level-$\ell$ slot as $x$, whose Drinfeld slot is `RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ`, namely the same curve with sections replaced by the $\mathbb Z$-linear combinations $g_{00}P+g_{10}Q$ and $g_{01}P+g_{11}Q$ formed in $\mathcal G\,T\,x.\mathrm{curve}\,h\Delta$, and such that $\rho$ sends the class of $x$ to the class of $x'$.
--
--   This is the action of a matrix $g\in M_2(\mathbb Z)$ with $\det g$ invertible modulo $q$ on the rigid moduli problem with combined $\Gamma_0(M')$, level-$\ell$ and Drinfeld-$\Gamma(q)$ structure: the automorphism acts only on the Drinfeld slot, and the conclusion pins its effect on raw data over every test algebra, not merely over fields. It is used in the construction of level relabelling for the fine moduli ring and in the identification of $\Gamma_0$-type level data built from linear combinations of a Drinfeld basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
    (q ℓ M' : ℕ) (hq : 2 ≤ q) (A : Type) [CommRing A]
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    ∃ ρ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,
      ∀ (T : Type) [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
        (hΔ : IsUnit x.level.2.2.curve.Δ),
        ∃ x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T,
          x'.curve = x.curve ∧ x'.level.1 = x.level.1 ∧ x'.level.2.1 = x.level.2.1 ∧
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ ∧
          ρ.act (Quot.mk _ x) = (Quot.mk _ x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt T) := by sorry
