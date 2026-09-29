-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/4b9eccc5-6be0-5fe1-a954-554da9483667
-- title:
--   Level automorphisms act on the Tate point by relabelling
-- statement:
--   Fix primes $q \ge 5$ and $\ell \ge 3$ with $\ell \ne q$, and $M' \ne 0$ with $q \nmid M'$ and $\ell \nmid M'$. Let $L$ be a field of characteristic $0$, $\xi \in L$ a primitive $q\ell$-th root of unity admitting a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota \xi = e^{2\pi i/(q\ell)}$, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the rational $q$-expansion field of $\Gamma_H$ at level $(q\ell)^2M'$, $H = \mathrm{levelH}\,(q\ell)\,M'$ the kernel of reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, $\ell$ and $M'$ units in $A$, and with $A$-algebra structure on $K$ compatible with $L$; let $j \in K$ be nonzero with Laurent expansion the coefficientwise image of the rational $j$-series. Assume: the variable-change stability of level-$\ell$ structures (`IsLevelPStructure`) and of the $\Gamma_0$-power kernel conditions (`IsGamma0PowAt` under `kernelVariableChangeDeg`); group laws $\mathcal{G}$ over $A$ satisfying chord–tangent and origin-identity; a level transport $\mathcal{T}$ at $q$ satisfying the section-transport condition; the existence of graded ring homomorphisms on projective models realising variable changes and coefficient maps. Write $R = \mathrm{rigidDataPow}\,A\,\ell\,M'\,q$, whose raw data over an $A$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with a $\Gamma_0$-power component (polynomials indexed by the prime factors of $M'$), a level-$\ell$ `LevelPData`, and a raw Drinfeld pair at $q$, points being variable-change classes. Let $\rho$ assign to each $\gamma \in \Gamma_0(M')$ an automorphism of the associated level moduli datum, and assume $\rho$ is pinned down on field points: for $T$ a field that is an $A$-algebra and raw data $x, x'$ over $T$ with the discriminant of the Drinfeld-pair curve of $x$ a unit, if $x'$ has the same curve and $\Gamma_0$-power component as $x$, its `LevelPData` is the $\gamma$-relabelling of that of $x$ and its Drinfeld pair is the $\gamma$-relabelling (via $\mathcal{G}$) of that of $x$, then $(\rho\,\gamma)$ carries the class of $x$ to the class of $x'$. The conclusion: there is a point $x_0$ of the moduli problem over $K$ whose $j$-invariant has Laurent expansion $\mathrm{jqNModC}\,L\,(q\ell)$, the $q$-expansion of $j$ in the variable $\mathsf{q}^{q\ell}$, such that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ which is a level automorphism at $\gamma^{-1}$ (that is, for all weights $k$, all weight-$k$ forms $f, g$ on $\Gamma_H$ at level $(q\ell)^2M'$ with integral $q$-expansions, $g$ nonzero, every $x \in K$ expanding as $f/g$, and every complex reading $\iota$ of $\xi$, the complex expansion of $\tau x$ times the $q$-expansion of $g \mid_k \mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}$ equals that of $f \mid_k \mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}$), the functorial transport of $x_0$ along $\tau$ (as an $A$-algebra map) equals $(\rho\,\gamma)$ applied to $x_0$.
--
--   This is the arithmetic-moduli form of the classical statement that the automorphisms of the field of modular functions attached to elements of $\Gamma_0(M')$ act on the Tate moduli point by relabelling its level structures, the $q$-expansion principle version of Shimura's reciprocity at the cusp. It is used in the analysis of the fibres of the full-level moduli problem, being cited in the proof that a certain residue-field tensor product of chart algebras is reduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow
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
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)

    (hρ : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A T]
      (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') :
    ∃ x₀ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K,
      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) ∧
      ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x₀ = (ρ ⟨γ, hγ⟩).act x₀ := by sorry
