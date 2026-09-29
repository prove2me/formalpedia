-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_of_isUnit_det_gamma0Pow
-- name    : ModularCurve.LevelRelabelling.exists_problemAut_relabel_of_isUnit_det_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/cb752c15-4892-5b1d-a565-fe2941e6a85c
-- title:
--   Relabelling by a matrix invertible mod qℓ gives problem automorphisms
-- statement:
--   Let $q$ and $\ell$ be primes with $\ell \ge 3$, let $M'$ be a nonzero natural number, and let $A$ be a commutative ring in which $\ell$ is invertible. Assume: `hℓ`, that for every $A$-algebra $T$ the predicate `IsLevelPStructure … ℓ` is preserved by applying a Weierstrass variable change $C$ to the curve and `LevelPData.variableChange C` to the data; `hM`, that `IsGamma0PowAt W p k h` is preserved by replacing $W$ by $C \bullet W$ and $h$ by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; a family of relative group laws $\mathcal G$ on the projective Weierstrass models over $A$-algebras with unit discriminant, which is chord–tangent (`IsChordTangent`) and has the origin as identity (`IsOriginIdentity`); a level transport $\mathcal T$ for level $q$ satisfying `IsSectionTransport`; and realisers `hVC`, `hCO` producing graded ring maps on the projective model rings implementing variable changes and coefficient maps, each surjective onto the irrelevant ideal in the required sense. Let $g \in M_2(\mathbb Z)$ have $\det g$ a unit in $\mathbb Z/q\ell$. Then the moduli datum `toLevelModuliDatum` of the rigidified problem `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` — whose $T$-points are variable-change classes of quadruples (a Weierstrass curve over $T$ with unit discriminant, a tuple of prime-power kernel generators at the prime factors of $M'$, a level-$\ell$ datum, and a Drinfeld $q$-pair) — admits two automorphisms $\sigma, \sigma'$ (each an assignment on $T$-points commuting with base change along $A$-algebra maps and preserving $j$) such that $\sigma' \circ \sigma$ and $\sigma \circ \sigma'$ are the identity on points over every $A$-algebra; for every field $T$ over $A$ and raw data $x, x'$ over $T$ with a unit witness $h\Delta$ for the discriminant of the curve underlying the Drinfeld slot of $x$, if $x'$ has the same curve and the same $\Gamma_0$-tuple as $x$, its level-$\ell$ datum is `LevelPData.relabel` of that of $x$ by $g$, and its Drinfeld pair is `RawDrinfeldPair.relabel` of that of $x$ by $g$, then $\sigma$ sends the class of $x$ to the class of $x'$; and there is $g' \in M_2(\mathbb Z)$ with $gg' \equiv g'g \equiv 1$ modulo $q\ell$ for which $\sigma'$ satisfies the same field-valued relabelling property with $g'$ in place of $g$.
--
--   This is the Katz–Mazur style statement that right multiplication by an integral matrix invertible modulo the level relabels the full level structures and induces an invertible automorphism of the rigidified moduli problem, here in the version where the $\Gamma_0$-part is a tuple of prime-power kernel generators for an arbitrary modulus $M'$ and is carried along unchanged. It supplies the group of relabellings used in the full-level analysis of the modular curve, in particular for transitivity arguments on Tate-type points, for counting minimal primes of the classifying algebra and for density statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_of_isUnit_det_gamma0Pow.lean

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

theorem ModularCurve.LevelRelabelling.exists_problemAut_relabel_of_isUnit_det_gamma0Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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

    (g : Matrix (Fin 2) (Fin 2) ℤ) (hdet : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) :
    ∃ σ σ' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T), σ'.act (σ.act y) = y) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T), σ.act (σ'.act y) = y) ∧

      (∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve g x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ →
          σ.act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∃ g' : Matrix (Fin 2) (Fin 2) ℤ,
        (g * g').map (Int.castRingHom (ZMod (q * ℓ))) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod (q * ℓ))) = 1 ∧
        (∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve g' x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' x.level.2.2 hΔ →
          σ'.act (Quot.mk _ x) = Quot.mk _ x')) := by sorry
