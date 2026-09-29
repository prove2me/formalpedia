-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
-- name    : GoodReductionJacobian.BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/67a18e7b-ef19-52c8-9838-70898aeed0a5
-- title:
--   Base change of a bare deformation with formal coordinates
-- statement:
--   Let $B' \xrightarrow{\varphi} B$ be a ring homomorphism between commutative rings, let $B_1$ be a commutative ring equipped with $B'$- and $B$-algebra structures, and assume the compatibility $(\,B \to B_1) \circ \varphi = (B' \to B_1)$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ carrying a relative group law $L_1$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} B_1$, with associativity, unit, inverse and naturality axioms), let $\hat G_1$ be a $d$-dimensional multivariable formal group law over $B_1$, and let $\theta_1$ be a system of formal coordinates for $f_1$ in dimension $d$, i.e. an assignment to each $B_1$-algebra $B''$ and each tuple $s \in (B'')^d$ of a point $\operatorname{Spec} B'' \to A_1$ over $\operatorname{Spec} B_1$. Let $P$ be a bare deformation of $(f_1, L_1)$ to $B'$: a scheme $P.A \to \operatorname{Spec} B'$ with a relative group law $P.L$ that is commutative, smooth and proper with connected fibres, together with $P.g : A_1 \to P.A$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B'$ cartesian and multiplicative on points. Let $G_P$ be a deformation of $\hat G_1$ to $B'$, i.e. a formal group law $G_P.F$ over $B'$ with $(G_P.F)$ mapping to $\hat G_1$ under $B' \to B_1$, let $\theta_P$ be formal coordinates for $P.f$, assume $P.L$ has law $G_P.F$ in the coordinates $\theta_P$ (naturality in algebra maps; for every $B'$-algebra with an ideal $J$ satisfying $J^{n+1} = 0$, the tuples in $J$ parametrise exactly the $J$-infinitesimal points injectively, and $\theta_P$ carries the truncated multiplication $\mathrm{nilMul}$ of $G_P.F$ to $P.L$), and assume $\theta_P$ lifts $\theta_1$ in the sense that $(\theta_1 B'' s) \text{ followed by } P.g = \theta_P B'' s$ for nilpotent tuples over $B'$-algebras that are $B_1$-algebras compatibly. Then there exist a bare deformation $D$ of $(f_1, L_1)$ to $B$ and a morphism $h : D.A \to P.A$ such that $h$, $D.f$, $P.f$, $\operatorname{Spec} \varphi$ form a cartesian square, $D.g$ followed by $h$ equals $P.g$, and $h$ is multiplicative: for every $T$-point pair $x, y$ of $D.f$ over $t : T \to \operatorname{Spec} B$, the product $D.L.\mathrm{mul}\,t\,x\,y$ followed by $h$ is the $P.L$-product of $x$ followed by $h$ and $y$ followed by $h$ over $t$ followed by $\operatorname{Spec}\varphi$. Moreover there exist a deformation $G$ of $\hat G_1$ to $B$ and formal coordinates $\theta$ for $D.f$ with $G.F = (G_P.F)$ pushed forward along $\varphi$, with $G.F$ commutative whenever $G_P.F$ is, with $D.L$ having law $G.F$ in the coordinates $\theta$, with $\theta$ lifting $\theta_1$ through $D.g$, and such that for every $B$-algebra $B''$ and every tuple $s \in (B'')^d$ of nilpotent elements, $\theta B'' s$ followed by $h$ equals $\theta_P B'' s$, where $B''$ is viewed as a $B'$-algebra through $\varphi$.
--
--   This is the base-change construction $D = P \otimes_{B'} B$ for bare deformations of a scheme with relative group law along a ring map $\varphi : B' \to B$ compatible with the maps to the ring $B_1$ over which the object being deformed lives, carried out simultaneously for the deformation of the formal group law and its system of formal coordinates. It supplies the transport of deformation data used in the regluing and tangent-coordinate comparisons; the abelian-scheme property bundle of the base-changed family comes from [`GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (φ : B' →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    {d : ℕ} (Ĝ₁ : MvFormalGroup d B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ d)
    (P : BareDeformation f₁ L₁ B')
    (GP : MvFormalGroup.Deformation Ĝ₁ B') (θP : RelativeGroupLaw.FormalCoordinates P.f d)
    (hθP : P.L.IsFormalCoordinates GP.F θP) (hlP : P.LiftsCoordinates θ₁ θP) :
    ∃ (D : BareDeformation f₁ L₁ B) (h : D.A ⟶ P.A)
      (hc : IsPullback h D.f P.f (Spec.map (CommRingCat.ofHom φ))),
      D.g ≫ h = P.g ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (x y : SchemeHomOver t D.f),
        (D.L.mul t x y).1 ≫ h =
          (P.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ h, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ h, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      ∃ (G : MvFormalGroup.Deformation Ĝ₁ B) (θ : RelativeGroupLaw.FormalCoordinates D.f d),
        G.F = GP.F.map φ ∧
        (GP.F.IsComm → G.F.IsComm) ∧
        D.L.IsFormalCoordinates G.F θ ∧ D.LiftsCoordinates θ₁ θ ∧
        ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (s : Fin d → B''), (∀ i, IsNilpotent (s i)) →
          letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
          (θ B'' s).1 ≫ h = (θP B'' s).1 := by sorry
