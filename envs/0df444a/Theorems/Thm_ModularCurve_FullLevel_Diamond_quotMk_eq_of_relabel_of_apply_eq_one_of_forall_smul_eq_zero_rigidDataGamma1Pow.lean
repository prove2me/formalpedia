-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_quotMk_eq_of_relabel_of_apply_eq_one_of_forall_smul_eq_zero_rigidDataGamma1Pow
-- name    : ModularCurve.FullLevel.Diamond.quotMk_eq_of_relabel_of_apply_eq_one_of_forall_smul_eq_zero_rigidDataGamma1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/fb303286-5c8c-50e1-a68d-13683051b234
-- title:
--   Trivial-diamond Γ₀(M')-relabelling fixes supersingular Γ₁(ℓ_g)-points
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ dividing $M'$ (also given as a prime factor of $M'$). The ambient frame consists of: a valuation subring $A$ of $\overline{\mathbb{Q}}$ for which $q$ is a nonunit (`A.LiesOverPrime q`); a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` whose members are exactly those of `ssPlaces q M' (ResidueField A)`, together with a chosen element $s \in W$; the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`, the latter being the level-$(q^2M')$ function field attached to `levelH q M'`, the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$; a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC (ResidueField A) M'`, compatible with coefficientwise reduction of Laurent series over $A$; an intermediate field $k_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ and $\pi_0 \in k_0$ lying in $A$ such that $A_0 := A \cap k_0$ is a henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field $\kappa$, every element of $A$ being congruent modulo the maximal ideal of $A$ to one coming from $k_0 \cap A$; a primitive $q$-th root of unity $\xi \in k_0$ admitting a ring homomorphism $k_0 \to \mathbb{C}$ sending $\xi$ to $e^{2\pi i/q}$; the subgroup $H_1 \le (\mathbb{Z}/q^2M')^\times$ of units congruent to $1$ both modulo $q$ and modulo $\ell_g$; the field $K$ obtained inside Laurent series over $k_0$ as the base change of `xHFunctionField (q ^ 2 * M') H₁`, an $A_0$-algebra in a scalar tower over $k_0$, and an element $j \in K$ whose Laurent series is the $q$-expansion `jq` of the modular invariant, assumed nonzero; hypotheses $h_\ell$ and $h_M$ saying that `IsGamma1Point` at $\ell_g$ and `IsGamma0PowAt` are preserved by Weierstrass variable changes (acting on level data by `LevelPData.variableChange` and `kernelVariableChangeDeg`); group laws $\mathcal{G}$ over $A_0$ that are chord–tangent and have the origin as identity; a level transport $\mathcal{T}$ for $q$ that is a section transport; and hypotheses `hVC`, `hCO` providing graded ring homomorphisms on projective models implementing variable changes and coefficient changes. Under these, let $x$ be a raw point of the rigid datum `rigidDataGamma1Pow A₀ ℓg M' q hℓ hM 𝒢 𝒯` over $\kappa$ such that the affine curve of $x$ has no nonzero $\kappa$-point annihilated by $q$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in `CongruenceSubgroup.Gamma0 M'` with $\gamma_{11} \equiv 1$ in $\mathbb{Z}/\ell_g$, let $x_1$ be a further raw point, and let $h_\Delta$ witness that the discriminant of the projective curve of the Drinfeld component `x.level.2.2` is a unit. If $x_1$ and $x$ have the same curve and the same $\Gamma_0$-power component, if the point `toPoint` attached to the $\Gamma_1$-coordinates $(x_P, y_P)$ of $x_1$ on the base change of $x$'s curve to $\kappa$ equals $\gamma_{00}$ times the corresponding point of $x$, if the $Q$-coordinates of $x_1$'s $\Gamma_1$-datum coincide with its $P$-coordinates, and if the Drinfeld pair of $x_1$ is `RawDrinfeldPair.relabel 𝒢 γ x.level.2.2 hΔ`, that is $(P,Q) \mapsto (\gamma_{00}P + \gamma_{10}Q,\ \gamma_{01}P + \gamma_{11}Q)$ formed with the relative group law, then $x_1$ and $x$ have the same class in the point set `Pt` of the rigid datum over $\kappa$.
--
--   This is the form, for the $\Gamma_1(\ell_g)$-guarded rigid moduli problem with trivial diamond condition, of the rigidity of level structures in a supersingular special fibre: on a curve with no nonzero $q$-torsion over the algebraically closed residue field, relabelling the Drinfeld $\Gamma(q)$-pair and the $\Gamma_1(\ell_g)$-point by $\gamma$ does not change the isomorphism class. It feeds the computation of the action of level automorphisms at supersingular places, [`ModularCurve.FullLevel.Diamond.levelAut_sub_self_mem_of_isLevelAutAt_of_mem_gamma0_of_apply_eq_one_of_over_ssPlace_rigidDataGamma1Pow`](thm.html#ModularCurve.FullLevel.Diamond.levelAut_sub_self_mem_of_isLevelAutAt_of_mem_gamma0_of_apply_eq_one_of_over_ssPlace_rigidDataGamma1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_quotMk_eq_of_relabel_of_apply_eq_one_of_forall_smul_eq_zero_rigidDataGamma1Pow.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule

theorem ModularCurve.FullLevel.Diamond.quotMk_eq_of_relabel_of_apply_eq_one_of_forall_smul_eq_zero_rigidDataGamma1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hℓgpf : ℓg ∈ M'.primeFactors)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    ∀ (x : (WeierstrassCurve.DrinfeldGlobal.rigidDataGamma1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM 𝒢 𝒯).Raw (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),

      (∀ P : (x.curve).toAffine.Point, q • P = 0 → P = 0) →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓg) = 1 →
      ∀ (x₁ : (WeierstrassCurve.DrinfeldGlobal.rigidDataGamma1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM 𝒢 𝒯).Raw (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (hΔ : IsUnit x.level.2.2.curve.Δ),
        x₁.curve = x.curve →
        x₁.level.1 = x.level.1 →

        ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) x₁.level.2.1.xP x₁.level.2.1.yP =
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) x.level.2.1.xP x.level.2.1.yP →
        x₁.level.2.1.xQ = x₁.level.2.1.xP → x₁.level.2.1.yQ = x₁.level.2.1.yP →
        x₁.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
        (Quot.mk _ x₁ : (WeierstrassCurve.DrinfeldGlobal.rigidDataGamma1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM 𝒢 𝒯).Pt (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) = Quot.mk _ x := by sorry
