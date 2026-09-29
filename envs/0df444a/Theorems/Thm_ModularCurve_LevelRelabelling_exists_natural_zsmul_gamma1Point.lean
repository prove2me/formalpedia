-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
-- name    : ModularCurve.LevelRelabelling.exists_natural_zsmul_gamma1Point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/57df2ee0-8a68-5c47-a599-68904fc7df9f
-- title:
--   Natural [a]-multiplication on Γ₁(ℓ)-data over A-algebras
-- statement:
--   Let $A$ be a commutative ring, $\ell$ a prime with $3 \le \ell$ whose image in $A$ is a unit, and let $\mathcal{G}$ be a family of relative group laws assigning to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with $\Delta(W)$ a unit a relative group law on its projective model, assumed chord-tangent (each $\mathcal{G}\,T\,W\,h_\Delta$ admits a points evaluation) and origin-normalised (the identity section is cut out by a ring homomorphism from the origin chart ring sending $x/y$ and $z/y$ to $0$). Then there is an operation $\mathrm{diam}$ which, for every $A$-algebra $T$, Weierstrass curve $W$ over $T$ and integer $a$, transforms level data $D=(x_P,y_P,x_Q,y_Q)$ in $T$ into level data $\mathrm{diam}\,T\,W\,a\,D$, subject to the following, in each case for $\Delta(W)$ a unit and $D$ a $\Gamma_1(\ell)$-point (that is: $(x_P,y_P)$ satisfies the affine Weierstrass equation, $(W.\mathrm{pre}\Psi\,\ell)(x_P)=0$, and $x_Q=x_P$, $y_Q=y_P$). (1) If $T$ is a field and $\ell \nmid a$, the affine point attached to the $P$-coordinates of $\mathrm{diam}\,T\,W\,a\,D$ (the point $(x,y)$ when nonsingular, else $0$) equals $a$ times that attached to $(x_P,y_P)$ in $W^{\mathrm{aff}}$'s point group. (2) For $\ell \nmid a$, $\mathrm{diam}\,T\,W\,a\,D$ is again a $\Gamma_1(\ell)$-point. (3) For an $A$-algebra map $f : T \to T'$ and $\ell \nmid a$, $\mathrm{diam}$ commutes with applying $f$ coordinatewise to $D$ and to $W$. (4) For a variable change $C$ over $T$ and $\ell \nmid a$, $\mathrm{diam}\,T\,(C \bullet W)\,a\,(D^C) = (\mathrm{diam}\,T\,W\,a\,D)^C$. (5) $\mathrm{diam}\,T\,W\,a\,D$ depends on $a$ only through its class in $\mathbb{Z}/\ell$. (6) $\mathrm{diam}\,T\,W\,1\,D = D$, and $\mathrm{diam}\,T\,W\,b\,(\mathrm{diam}\,T\,W\,a\,D) = \mathrm{diam}\,T\,W\,(ab)\,D$ for $\ell \nmid a$, $\ell \nmid b$. (7) For $\ell \nmid a$, if $S$ is a section of the projective model passing through $(x_P,y_P)$, then the $a$-fold multiple $\mathrm{zsmulSection}\,(\mathcal{G}\,T\,W\,h_\Delta)\,a\,S$ passes through the $P$-coordinates of $\mathrm{diam}\,T\,W\,a\,D$.
--
--   This is the single-point (diamond) analogue of the Katz-style relabelling of level data: multiplication by $a$ on a point of exact order $\ell$, realised as an operation on coordinate data that is natural in the base $A$-algebra, equivariant for changes of Weierstrass coordinates and multiplicative in $a$ modulo $\ell$. It feeds the construction of the diamond operators on the $\Gamma_1(\ell^n)$-moduli data, in particular [`ModularCurve.LevelRelabelling.exists_isModuliRelabelling_rigidDataH1Pow`](thm.html#ModularCurve.LevelRelabelling.exists_isModuliRelabelling_rigidDataH1Pow) and the comparison of the $\Gamma_0$-action with relabelling on classified points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem ModularCurve.LevelRelabelling.exists_natural_zsmul_gamma1Point
    (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity) :
    ∃ diam : ∀ (T : Type) [CommRing T] [Algebra A T],
        WeierstrassCurve T → ℤ → ModularCurve.LevelPData T → ModularCurve.LevelPData T,

      (∀ (T : Type) [Field T] [DecidableEq T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          ModularCurve.LevelRelabelling.toPoint W (diam T W a D).xP (diam T W a D).yP =
            a • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          ModularCurve.IsGamma1Point W ℓ (diam T W a D)) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
          (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T' (W.map f.toRingHom) a (D.map f.toRingHom) = (diam T W a D).map f.toRingHom) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (C : WeierstrassCurve.VariableChange T) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T (C • W) a (D.variableChange C) = (diam T W a D).variableChange C) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a a' : ℤ)
          (haa' : (a : ZMod ℓ) = (a' : ZMod ℓ))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T W a D = diam T W a' D) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsGamma1Point W ℓ D), diam T W 1 D = D) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a b : ℤ)
          (ha : ¬ ((ℓ : ℤ) ∣ a)) (hb : ¬ ((ℓ : ℤ) ∣ b))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T W b (diam T W a D) = diam T W (a * b) D) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D)
          (S : Section W) (hS : IsSectionThrough S D.xP D.yP),
          IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) (diam T W a D).xP (diam T W a D).yP) := by sorry
