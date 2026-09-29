-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt
-- name    : GoodReductionJacobian.BareDeformation.range_subset_image_lev_of_mul_inv_one_pushPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/27c3ab17-cf61-5e78-a414-c2d74410ed3d
-- title:
--   Closure on points of the level image in a bare deformation
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B$ and $B_0$ be commutative rings with $B_0$ a $B$-algebra such that $\mathrm{algebraMap}\ B\ B_0$ is surjective with nilpotent kernel, let $E_0$ be a `FakeEllipticCurve` for $(\Lambda,N)$ over $B_0$ — in particular a scheme $E_0.A$ with structure morphism $E_0.f$ to $\operatorname{Spec} B_0$, a relative group law $E_0.L$, and a morphism $E_0.\mathrm{lev} : E_0.C \to E_0.A$ — and let $D$ be a `BareDeformation` of $(E_0.f, E_0.L)$ to $B$, so $D.A \to \operatorname{Spec} B$ carries a commutative relative group law $D.L$ together with $D.g : E_0.A \to D.A$ making the square over $\operatorname{Spec} B_0 \to \operatorname{Spec} B$ cartesian and compatible with the group laws on points. Let $\varphi : \iota \to \mathrm{End}(D.A)$ and $\varphi_0 : \iota \to \mathrm{End}(E_0.A)$ be families of endomorphisms over the respective bases, with $D.g \circ \varphi_0(i) = \varphi(i) \circ D.g$, and assume each $\varphi_0(i)$ preserves, on $T$-points over $\operatorname{Spec} B_0$, the property of factoring through $E_0.\mathrm{lev}$. Put $Z := |D.g|\bigl(\mathrm{range}\,|E_0.\mathrm{lev}|\bigr) \subseteq |D.A|$. Then: for every scheme $T$, every $t : T \to \operatorname{Spec} B$ and all $T$-points $P,Q$ of $D.A$ over $t$ whose topological images lie in $Z$, the images of $D.L.\mathrm{mul}\ t\ P\ Q$ and of $D.L.\mathrm{inv}\ t\ P$ lie in $Z$; the image of the unit section $D.L.\mathrm{one}\ t$ lies in $Z$; and for each $i$ the image of $P$ composed with $\varphi(i)$ lies in $Z$ whenever that of $P$ does.
--
--   This is the verification that the set-theoretic image of the level structure of a fake elliptic curve, transported along a nilpotent thickening of the base through the cartesian morphism of a bare deformation, is closed under the relative group law and under the given lifted endomorphisms at the level of underlying topological spaces. It feeds [`GoodReductionJacobian.BareDeformation.levelPiece_points`](thm.html#GoodReductionJacobian.BareDeformation.levelPiece_points), where this closed subset is assembled into a level piece of the deformed abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt.lean

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

theorem GoodReductionJacobian.BareDeformation.range_subset_image_lev_of_mul_inv_one_pushPt
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (φ₀ : ι → (E₀.A ⟶ E₀.A)) (hφ₀ : ∀ i, φ₀ i ≫ E₀.f = E₀.f) (hφg : ∀ i, φ₀ i ≫ D.g = D.g ≫ φ i)
    (hφ₀_stable : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P → FactorsThrough E₀.lev (pushPt (φ₀ i) (hφ₀ i) P)) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        Set.range P.1.base ⊆ D.g.base '' Set.range E₀.lev.base → Set.range Q.1.base ⊆ D.g.base '' Set.range E₀.lev.base →
          Set.range (D.L.mul t P Q).1.base ⊆ D.g.base '' Set.range E₀.lev.base ∧
            Set.range (D.L.inv t P).1.base ⊆ D.g.base '' Set.range E₀.lev.base) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)),
        Set.range (D.L.one t).1.base ⊆ D.g.base '' Set.range E₀.lev.base) ∧
    (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        Set.range P.1.base ⊆ D.g.base '' Set.range E₀.lev.base →
          Set.range (pushPt (φ i) (hφ i) P).1.base ⊆ D.g.base '' Set.range E₀.lev.base) := by sorry
