-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_levelModuliPackageAbs_restrictScalars_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_levelModuliPackageAbs_restrictScalars_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/fcc746bb-8740-5fe9-992d-63fb83305372
-- title:
--   Base change of the abstract full-level moduli package
-- statement:
--   Let $A_0$ be a commutative ring, let $A$ be a commutative $A_0$-algebra, and let $q,\ell,N$ be natural numbers. Assume four variable-change transport hypotheses, two for $A_0$-algebras and two for $A$-algebras: for every such base ring $T$, every Weierstrass curve $W$ over $T$ and every Weierstrass variable change $C$, a level-$\ell$ datum $D=(x_P,y_P,x_Q,y_Q)$ satisfying the affine equation at both points, vanishing of $(W.\mathrm{pre}\Psi\,\ell)$ at $x_P$ and $x_Q$, and invertibility of both independence elements, transforms to such a datum for $C\bullet W$; and a polynomial $h$ with $\mathrm{IsGamma0PowAt}\;W\;p\;k\;h$ (for $p^k=2$: $\deg h\le 1$, coefficient $1$ in degree $1$, $h\mid W.\Psi_2^{\mathrm{Sq}}$; otherwise $\deg h\le\varphi(p^k)/2$, coefficient $1$ in degree $\varphi(p^k)/2$, $h\cdot W.\mathrm{pre}\Psi(p^{k-1})\mid W.\mathrm{pre}\Psi(p^k)$, and $h\mid W.\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h$ for all $a$ with $2\le a\le (p^k-1)/2$, $p\nmid a$) transforms to one for $C\bullet W$ after the degree-$\mathrm{gamma0PowDeg}(p,k)$ kernel variable change. Let $\mathcal{G}_0$ be a family of relative group laws on the projective models of discriminant-unit Weierstrass curves over $A_0$-algebras, $\mathcal{T}_0$ a level-$q$ transport of raw Drinfeld pairs for it, and $P_0$ an abstract fine moduli package, with representing ring $B_0$ and universal point, for the moduli datum attached to the rigidified level component $\Gamma_0$-prime-power $\times$ level-$\ell$ $\times$ Drinfeld level-$q$ over $A_0$. Then there exist a package $P$ for the corresponding datum over $A$ formed from the scalar restrictions $\mathcal{G}_0|_A$, $\mathcal{T}_0|_A$, and a ring homomorphism $\varphi:P_0.B_0\to P.B_0$, such that $\varphi$ commutes with the structure maps from $A_0$ (via $A$), such that for every $A$-algebra $T$ and every ring map $g:P_0.B_0\to T$ agreeing with $A_0\to A\to T$ there is a unique $A$-algebra map $h:P.B_0\to T$ with $h\circ\varphi=g$, and such that for every $A$-algebra $T$ and every datum over $T$ consisting of a Weierstrass curve $W$ with $W.\Delta$ a unit, a family $h$ of polynomials indexed by the prime factors of $N$ with $\mathrm{IsGamma0PowAt}\;W\;p\;(v_p(N))\;(h\,p)$, a level-$\ell$ datum $D$, and a raw Drinfeld pair $z$ of level $q$ for $\mathcal{G}_0|_A$, the classifying map of the resulting point over $A$ composed with $\varphi$ equals the classifying map of the same point read over $A_0$ by restriction of scalars.
--
--   This is the base-change statement for the abstract fine moduli package of the full rigidified level structure ($\Gamma_0(N)$ in prime-power generator-kernel form, a level-$\ell$ structure, and a Drinfeld level-$q$ basis): the representing ring over $A$ is characterised as $A\otimes_{A_0}B_0$ by a universal property, compatibly with the classifying maps. It is used by the later statements about the representing ring over a discrete valuation ring, about minimal primes and their number, and about the range of the classifying maps on fixed $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_levelModuliPackageAbs_restrictScalars_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.exists_levelModuliPackageAbs_restrictScalars_gamma0Pow
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum) :
    ∃ (P : LevelModuliPackageAbs A
          (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
      (φ : P₀.B₀ →+* P.B₀),
      φ.comp (algebraMap A₀ P₀.B₀) = (algebraMap A P.B₀).comp (algebraMap A₀ A) ∧
      (∀ (T : Type u) [CommRing T] [Algebra A T] (g : P₀.B₀ →+* T),
          g.comp (algebraMap A₀ P₀.B₀) = (algebraMap A T).comp (algebraMap A₀ A) →
          ∃! h : P.B₀ →ₐ[A] T, h.toRingHom.comp φ = g) ∧
      (∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
          (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p)) (hD : ModularCurve.IsLevelPStructure W ℓ D)
          (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z),
          letI : Algebra A₀ T := algebraRestrict A₀ A T
          (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
              ((gamma0PowComponent A N hM).prod ((levelPComponent A ℓ hℓ).prod
                (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).Raw T))).toRingHom.comp φ =
          (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
              ((gamma0PowComponent A₀ N hM₀).prod ((levelPComponent A₀ ℓ hℓ₀).prod
                (levelComponent A₀ 𝒢₀ q 𝒯₀))).Raw T))).toRingHom) := by sorry
