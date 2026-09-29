-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_levelPiece_points
-- name    : GoodReductionJacobian.BareDeformation.levelPiece_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/5874da3c-2faf-5429-ba53-f21727cb9d55
-- title:
--   Group-law and level stability of the lifted level piece W
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B$ be a commutative local Artinian ring and $B_0$ a commutative $B$-algebra such that the structure map $B \to B_0$ is surjective (`hπ`) with nilpotent kernel (`hker`), and suppose $N$ is a unit in $B$ (`hN`). Let $E_0$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $B_0$ and let $D$ be a `BareDeformation` of $(E_0.f, E_0.L)$ to $B$, so that $D$ provides a scheme $D.A$ with structure morphism $D.f$ to $\operatorname{Spec} B$, a relative group law $D.L$, and a morphism $D.g : E_0.A \to D.A$ exhibiting $E_0.f$ as the base change of $D.f$ along $B \to B_0$; $D.f$ is assumed smooth of relative dimension $2$. Let $\varphi : \iota \to \operatorname{End}(D.A)$ be endomorphisms over $\operatorname{Spec} B$ ($\varphi_i$ followed by $D.f$ equals $D.f$) which are homomorphisms for $D.L$ on points (`hφ_hom`), and let $\varphi_0 : \iota \to \operatorname{End}(E_0.A)$ be endomorphisms over $\operatorname{Spec} B_0$ with $\varphi_{0,i}$ followed by $D.g$ equal to $D.g$ followed by $\varphi_i$, each $\varphi_{0,i}$ carrying points that factor through $E_0.\mathrm{lev}$ to points that factor through $E_0.\mathrm{lev}$. Finally let $W$ be an open subscheme of $D.L.\mathrm{schemeKer}\,N$, the pullback of $D.L.\mathrm{schemeNsmul}\,N$ against the identity section $D.L.\mathrm{one}$, whose underlying set is the preimage under the base map of $\mathrm{pullback.fst}$ of the image under $D.g$ of the range of the base map of $E_0.\mathrm{lev}$. Write $\mathrm{lev}$ for the composite of the open immersion $W.\iota$ with $\mathrm{pullback.fst}$. The conclusion is the conjunction of five assertions, where a point of $D.A$ over $t : T \to \operatorname{Spec} B$ is a morphism $P : T \to D.A$ with $P$ followed by $D.f$ equal to $t$, and "factors through $\mathrm{lev}$" means $P = P_0$ followed by $\mathrm{lev}$ for some $P_0 : T \to W$: (i) if $P$ and $Q$ factor through $\mathrm{lev}$ then so do $D.L.\mathrm{mul}\,t\,P\,Q$ and $D.L.\mathrm{inv}\,t\,P$; (ii) the unit $D.L.\mathrm{one}\,t$ factors through $\mathrm{lev}$; (iii) if $P$ factors through $\mathrm{lev}$ then $\mathrm{nsmulPt}\,D.L\,t\,N\,P = D.L.\mathrm{one}\,t$; (iv) each $\varphi_i$ preserves the property of factoring through $\mathrm{lev}$; (v) for every $t' : T \to \operatorname{Spec} B_0$ and every point $P$ of $E_0.A$ over $t'$ factoring through $E_0.\mathrm{lev}$, the composite of $P$ with $D.g$ factors through $\mathrm{lev}$.
--
--   This records that the open piece $W$ of the $N$-torsion of a bare deformation $D$ cut out by the level locus of $E_0$ behaves, on points, like a level structure: it is stable under the group law, contains the unit, consists of $N$-torsion points, is stable under the given endomorphisms, and receives the level points of $E_0$ along $D.g$. It is the point-theoretic input to [`GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension`](thm.html#GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension), which lifts the level structure of $E_0$ to the deformation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_levelPiece_points.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.BareDeformation.levelPiece_points
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f]
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (hφ_hom : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
      pushPt (φ i) (hφ i) (D.L.mul t P Q) = D.L.mul t (pushPt (φ i) (hφ i) P) (pushPt (φ i) (hφ i) Q))
    (φ₀ : ι → (E₀.A ⟶ E₀.A)) (hφ₀ : ∀ i, φ₀ i ≫ E₀.f = E₀.f) (hφg : ∀ i, φ₀ i ≫ D.g = D.g ≫ φ i)
    (hφ₀_stable : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P → FactorsThrough E₀.lev (pushPt (φ₀ i) (hφ₀ i) P))
    (W : (D.L.schemeKer N).Opens)
    (hW : (W : Set ↥(D.L.schemeKer N)) = ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base))) :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) P → FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) Q → FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) (D.L.mul t P Q) ∧ FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) (D.L.inv t P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)), FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) (D.L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) P → nsmulPt D.L t N P = D.L.one t) ∧
      (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) P → FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) (pushPt (φ i) (hφ i) P)) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ (W : Scheme.{0}), P₀ ≫ (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) = P.1 ≫ D.g) := by sorry
