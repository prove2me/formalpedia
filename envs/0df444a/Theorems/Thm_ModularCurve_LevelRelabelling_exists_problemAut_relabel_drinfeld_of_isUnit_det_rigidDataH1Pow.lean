-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_drinfeld_of_isUnit_det_rigidDataH1Pow
-- name    : ModularCurve.LevelRelabelling.exists_problemAut_relabel_drinfeld_of_isUnit_det_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/e4367d22-291c-54e6-89ca-dd4cd46c685e
-- title:
--   Relabelling the Drinfeld pair by g gives a moduli automorphism
-- statement:
--   Let $A$ be a commutative ring, $q$ a prime, and $\ell_g$, $M'$ natural numbers with $M' \neq 0$. Three transport hypotheses are imposed for all $A$-algebras $T$: `hℓ`, that the conditions `IsGamma1Point` (a point $(x_P,y_P)$ on the affine Weierstrass equation with $(\operatorname{pre}\Psi_{\ell_g})(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$) are preserved by the variable-change action on `LevelPData`; `hM`, that `IsGamma0PowAt W p k h` implies `IsGamma0PowAt (C • W) p k` for `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that divisibility of `inLineMulPoly W ℓg n x` by $h$ is transported to the variable-changed polynomial at $u^{-2}(x-r)$. Further, $\mathcal{G}$ is a family of relative group laws on the projective models of elliptic Weierstrass curves over $A$-algebras, assumed chord–tangent and with the origin as identity section, $\mathcal{T}$ a level transport of Drinfeld pairs at $q$ satisfying `IsSectionTransport`, and `hVC`, `hCO` assert that every variable change and every $A$-algebra map is realised by a graded ring homomorphism of the projective-model graded quotient rings satisfying the irrelevant-ideal condition. Finally $g$ is a $2 \times 2$ integer matrix whose determinant is a unit in $\mathbb{Z}/q$. Write $\mathcal{D}$ for the level moduli datum attached to `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯`, whose raw objects over an $A$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with a $\Gamma_0$-component (a monic kernel polynomial for each prime factor of $M'$), a $\Gamma_1(\ell_g)$-point and a Drinfeld basis pair of level $q$, subject to the link condition `IsGamma1Link`, and whose points over $T$ are such raw objects modulo variable change. The assertion is that there exist $\sigma, \sigma'$ in $\mathcal{D}$.`ProblemAut`, that is, self-maps of the point functor natural in $T$ and preserving the $j$-invariant, such that $\sigma' \circ \sigma$ and $\sigma \circ \sigma'$ are the identity on points over every $A$-algebra, such that for every field $T$ over $A$ and raw objects $x, x'$ over $T$ with $x'$ having the same curve, the same $\Gamma_0$-component and the same $\Gamma_1(\ell_g)$-point as $x$ and with Drinfeld pair `RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ`, namely the pair $(\,[g_{00}]P + [g_{10}]Q,\ [g_{01}]P + [g_{11}]Q\,)$ formed with the group law $\mathcal{G}$ on the curve, one has $\sigma$ sending the class of $x$ to the class of $x'$, and such that there is an integer matrix $g'$ with $gg'$ and $g'g$ both congruent to the identity modulo $q$ for which $\sigma'$ satisfies the same relabelling description with $g'$ in place of $g$.
--
--   This is the $\mathrm{GL}_2(\mathbb{Z}/q)$-action on full level-$q$ (Drinfeld basis) structures, as in Katz–Mazur, realised here as an invertible automorphism of the moduli problem for the combined $\Gamma_0(M') \cap \Gamma_1(\ell_g) \cap \Gamma(q)$ datum, the remaining level components being left untouched. It is used in the analysis of the fibres and of the Galois action on the corresponding moduli space, and is cited by the statements on minimal primes and on Galois conjugation of the classifying maps for this datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_drinfeld_of_isUnit_det_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.exists_problemAut_relabel_drinfeld_of_isUnit_det_rigidDataH1Pow
    (A : Type) [CommRing A] (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) [NeZero M']
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

    (g : Matrix (Fin 2) (Fin 2) ℤ) (hdet : IsUnit (g.map (Int.castRingHom (ZMod q))).det) :
    ∃ σ σ' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt T), σ'.act (σ.act y) = y) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt T), σ.act (σ'.act y) = y) ∧

      (∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ →
          σ.act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∃ g' : Matrix (Fin 2) (Fin 2) ℤ,
        (g * g').map (Int.castRingHom (ZMod q)) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod q)) = 1 ∧
        (∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' x.level.2.2 hΔ →
          σ'.act (Quot.mk _ x) = Quot.mk _ x')) := by sorry
