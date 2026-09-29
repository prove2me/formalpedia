-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/10abb02d-82c2-5430-ab4f-d6c40750ffba
-- title:
--   Base change of the abstract H₁ level-moduli package
-- statement:
--   Fix commutative rings $A_0$ and $A$ in one universe with $A$ an $A_0$-algebra, and natural numbers $q,\ell,N$. Assume, both for all $A_0$-algebras $T$ (hypotheses `hℓ₀`, `hM₀`, `hL₀`) and for all $A$-algebras $T$ (hypotheses `hℓ`, `hM`, `hL`), that variable changes $C$ of a Weierstrass curve $W$ over $T$ preserve the three level conditions: `IsGamma1Point W ℓ D` (the point $(x_P,y_P)$ satisfies the affine equation, $\mathrm{preΨ}_\ell$ vanishes at $x_P$, and $(x_Q,y_Q)=(x_P,y_P)$) passes to `D.variableChange C`; `IsGamma0PowAt W p k h` passes to `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and divisibility $h \mid \mathrm{inLineMulPoly}\,W\,\ell\,n\,x$ passes to $\mathrm{kernelVariableChangeDeg}\,C\,d\,h \mid \mathrm{inLineMulPoly}\,(C\bullet W)\,\ell\,n\,(u^{-2}(x-r))$. Let $\mathcal G_0$ be a system of relative group laws on projective Weierstrass models over $A_0$-algebras, $\mathcal T_0$ a level transport for $\mathcal G_0$ and $q$, and let $P_0$ be an abstract level-moduli package over $A_0$ for the datum `rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀`, that is, an $A_0$-algebra $B_0$ with a universal point which represents the functor of variable-change classes of raw data. Then there are an abstract package $P$ over $A$ for the corresponding datum formed from the scalar restrictions of $\mathcal G_0$ and $\mathcal T_0$, and a ring homomorphism $\varphi : P_0.B_0 \to P.B_0$, such that: $\varphi$ composed with $A_0 \to P_0.B_0$ equals $A_0 \to A \to P.B_0$; for every $A$-algebra $T$ and every ring homomorphism $g : P_0.B_0 \to T$ whose restriction to $A_0$ is $A_0 \to A \to T$ there is a unique $A$-algebra homomorphism $h : P.B_0 \to T$ with $h \circ \varphi = g$ (so $(P.B_0,\varphi)$ is the pushout of $P_0.B_0$ along $A_0 \to A$); and the classifying maps agree, in the sense that for every $A$-algebra $T$, Weierstrass curve $W$ over $T$ with $W.\Delta$ a unit, family $h$ of polynomials indexed by the prime factors of $N$, level-$p$ datum $D$, raw Drinfeld pair $z$, and proofs that each $h\,p$ satisfies `IsGamma0PowAt W p (N.factorization p)`, that $D$ is a $\Gamma_1$-point for $\ell$, that $z$ is a Drinfeld level-$q$ structure for the restricted group laws on $W$, and that the link condition `IsGamma1Link W ℓ N h D` holds, the $A$-algebra classifying map of the class of $(W,h,D,z)$ for $P$, composed with $\varphi$, coincides with the $A_0$-algebra classifying map of the same datum for $P_0$, $T$ being viewed as an $A_0$-algebra through $A_0 \to A \to T$.
--
--   This is the base-change statement for the representing ring of the moduli problem combining $\Gamma_0(N)$-type cyclic kernel generators, a $\Gamma_1(\ell)$-point linked to the $\ell$-part of $N$, and a Drinfeld level-$q$ basis: the package over $A$ may be taken to be $A \otimes_{A_0} P_0.B_0$, compatibly with classification of level data. It feeds the local study of the resulting ring, including flatness over a discrete valuation ring, reducedness of fibres at minimal primes, and the description of its adic completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ N : ℕ)
    (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢₀ : GroupLaws A₀) (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum) :
    ∃ (P : LevelModuliPackageAbs A
          (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
      (φ : P₀.B₀ →+* P.B₀),
      φ.comp (algebraMap A₀ P₀.B₀) = (algebraMap A P.B₀).comp (algebraMap A₀ A) ∧
      (∀ (T : Type u) [CommRing T] [Algebra A T] (g : P₀.B₀ →+* T),
          g.comp (algebraMap A₀ P₀.B₀) = (algebraMap A T).comp (algebraMap A₀ A) →
          ∃! h : P.B₀ →ₐ[A] T, h.toRingHom.comp φ = g) ∧
      (∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
          (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p)) (hD : ModularCurve.IsGamma1Point W ℓ D)
          (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z) (hlk : ModularCurve.IsGamma1Link W ℓ N h D),
          letI : Algebra A₀ T := algebraRestrict A₀ A T
          (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A N hM).prod ((gamma1Component A ℓ hℓ).prod
                (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom.comp φ =
          (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A₀ N hM₀).prod ((gamma1Component A₀ ℓ hℓ₀).prod
                (levelComponent A₀ 𝒢₀ q 𝒯₀))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL₀ _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom) := by sorry
