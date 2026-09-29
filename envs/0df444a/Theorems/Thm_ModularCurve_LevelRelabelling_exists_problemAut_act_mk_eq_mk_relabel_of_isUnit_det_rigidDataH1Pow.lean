-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_rigidDataH1Pow
-- name    : ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/dd82159d-07bf-5b6c-ae47-9f275e1cc64f
-- title:
--   Drinfeld slot relabelling by g is a problem automorphism
-- statement:
--   Fix natural numbers $q$, $\ell_g$, $M'$ with $2\le q$ and a commutative ring $A$. Assume: `hℓ`, that for every $A$-algebra $T$, Weierstrass curve $W$ over $T$, variable change $C$ and level-$p$ datum $D=(x_P,y_P,x_Q,y_Q)$, the predicate `IsGamma1Point` for $W,\ell_g,D$ (the affine equation at $(x_P,y_P)$, vanishing of $(W.\mathrm{pre}\Psi\,\ell_g)$ at $x_P$, and $x_Q=x_P$, $y_Q=y_P$) passes to $C\bullet W$ and $D$ transformed by $C$; `hM`, that `IsGamma0PowAt` at $(p,k)$ passes from $h$ to `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; `hL`, that divisibility of `inLineMulPoly W ℓg n x` by $h$ passes to the corresponding statement for $C\bullet W$ and $((C.u^{-1})^2(x-C.r))$. Fix further a family of relative group laws $\mathcal G$ on the projective models, chord–tangent (`IsChordTangent`) and with origin section the identity (`IsOriginIdentity`), a level transport $\mathcal T$ for $\mathcal G$ at level $q$ satisfying `IsSectionTransport`, and hypotheses `hVC`, `hCO` supplying, for every variable change and every $A$-algebra map, a graded ring homomorphism between projective-model graded rings that is a variable-change hom, respectively a coefficient hom, and whose image contains the irrelevant ideal. Let $g\in M_2(\mathbb Z)$ have $\det g$ a unit in $\mathbb Z/q$. Then the level moduli datum attached to `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯` admits a problem automorphism $\rho$ (an operation on points natural in the test algebra and preserving $j$) such that for every $A$-algebra $T$, every raw datum $x$ over $T$ and every proof $h_\Delta$ that the discriminant of the projective curve in the Drinfeld slot of $x$ is a unit, there is a raw datum $x'$ over $T$ with the same Weierstrass curve, the same $\Gamma_0(M')$-slot family of polynomials, the same $\Gamma_1(\ell_g)$-point, whose Drinfeld slot is `RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ`, i.e. the pair of sections $(P,Q)$ replaced by the $\mathbb Z$-linear combinations with coefficient columns of $g$, and with $\rho$ applied to the class of $x$ equal to the class of $x'$ in the quotient by the variable-change relation.
--
--   This is the Katz–Mazur action of a matrix $g$ with $\det g$ invertible mod $q$ on Drinfeld $\Gamma(q)$-structures, realised here as an automorphism of the moduli problem of type $\Gamma_0(M')\cap\Gamma_1(\ell_g)$ together with a Drinfeld basis, leaving the curve and the $\Gamma_0$, $\Gamma_1$ slots untouched. It supplies the relabelling automorphisms used in the construction of level-structure automorphisms on the associated moduli points and in the diamond-operator computation at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_rigidDataH1Pow
    (q ℓg M' : ℕ) (hq : 2 ≤ q) (A : Type) [CommRing A]
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    ∃ ρ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut,
      ∀ (T : Type) [CommRing T] [Algebra A T] (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T)
        (hΔ : IsUnit x.level.2.2.curve.Δ),
        ∃ x' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T,
          x'.curve = x.curve ∧ x'.level.1 = x.level.1 ∧ x'.level.2.1 = x.level.2.1 ∧
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ ∧
          ρ.act (Quot.mk _ x) = (Quot.mk _ x' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T) := by sorry
