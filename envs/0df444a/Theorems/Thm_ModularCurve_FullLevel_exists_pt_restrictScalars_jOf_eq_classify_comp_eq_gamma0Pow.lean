-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/6a070c1b-2d9d-5276-a634-a0b1bd62cefd
-- title:
--   Restriction of full-level points along A₀ → A
-- statement:
--   Fix commutative rings $A_0$ and $A$ with $A$ an $A_0$-algebra, and natural numbers $q$, $\ell$, $N$. Assume, over $A_0$-algebras and over $A$-algebras alike, two stability hypotheses: that a level-$p$ datum $D$ (four coordinates $x_P,y_P,x_Q,y_Q$) satisfying `IsLevelPStructure W ℓ D` — both points on the affine curve, both $x$-coordinates roots of $W.\mathrm{pre}\Psi_\ell$, and both independence elements units — transports to the variable change $C\bullet W$ via `LevelPData.variableChange`, and that `IsGamma0PowAt W p k h` (the two-kernel condition when $p^k=2$, otherwise the cyclic-generator condition on $h$) transports to $C\bullet W$ via `kernelVariableChangeDeg`. Fix group laws $\mathcal G_0$ on projective Weierstrass models over $A_0$-algebras, a level transport $\mathcal T_0$ at level $q$, and universal packages $P_0$ over $A_0$ and $P$ over $A$ for the rigidified datum `rigidDataPow`, whose raw points over $T$ are a Weierstrass curve $W$ with $\Delta$ a unit together with kernel polynomials $h(p)$ for $p \mid N$ at exponent $v_p(N)$, a level-$\ell$ structure $D$ and a Drinfeld pair $z$ at level $q$, modulo variable change; here the data over $A$ are the scalar restrictions of $\mathcal G_0,\mathcal T_0$. Let $\varphi : P_0.B_0 \to P.B_0$ be a ring homomorphism such that for every such raw tuple the classifying map of $P$ composed with $\varphi$ equals the classifying map of $P_0$. Then for every $A$-algebra $T$, viewed as an $A_0$-algebra through $A$, every point $x$ over $T$ of the $A_0$-datum admits a point $x'$ over $T$ of the $A$-datum with $j(x') = j(x)$ and with the classifying map of $x'$ composed with $\varphi$ equal to that of $x$.
--
--   This is the base-change statement for the full-level moduli problem in its prime-power $\Gamma_0$ form: points of the problem over $A_0$ are recovered as points of the problem over $A$ without changing the $j$-invariant, compatibly with the universal classifying maps. It is used where a point with prescribed $j$-invariant must be moved from the $A_0$-package to the $A$-package, in the analysis of minimal primes of the full-level chart and in the statement about classifying maps landing in a finite chart algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem ModularCurve.FullLevel.exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ N : ℕ)
    (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢₀ : GroupLaws A₀) (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum)
    (P : LevelModuliPackageAbs A
      (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
    (φ : P₀.B₀ →+* P.B₀)

    (hφ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
        (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
        (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p))
        (hD : ModularCurve.IsLevelPStructure W ℓ D)
        (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z),
        letI : Algebra A₀ T := algebraRestrict A₀ A T
        (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
            ((gamma0PowComponent A N hM).prod ((levelPComponent A ℓ hℓ).prod
              (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).Raw T))).toRingHom.comp φ =
        (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
            ((gamma0PowComponent A₀ N hM₀).prod ((levelPComponent A₀ ℓ hℓ₀).prod
              (levelComponent A₀ 𝒢₀ q 𝒯₀))).Raw T))).toRingHom)
    (T : Type u) [CommRing T] [Algebra A T] :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    ∀ x : (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.Pt T,
      ∃ x' : (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.Pt T,
        (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.jOf x' =
          (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.jOf x ∧
        (P.classify x').toRingHom.comp φ = (P₀.classify x).toRingHom := by sorry
