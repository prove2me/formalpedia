-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_levelPiece_unique
-- name    : GoodReductionJacobian.BareDeformation.levelPiece_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/98f9760b-86bd-574d-9f10-40ca3317c0da
-- title:
--   Uniqueness of the lifted level subscheme of a bare deformation
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B$ be a commutative local artinian ring and $B_0$ a commutative $B$-algebra such that $\operatorname{algebraMap} B B_0$ is surjective with nilpotent kernel, and assume $N$ is a unit in $B$. Let $E_0$ be a `FakeEllipticCurve` for $\Lambda$ and $N$ over $B_0$ (a scheme $E_0.A$ over $\operatorname{Spec} B_0$ with a commutative relative group law $E_0.L$, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action satisfying the trace condition, and a level structure $E_0.\mathrm{lev} : E_0.C \to E_0.A$), and let $D$ be a `BareDeformation` of $E_0.f, E_0.L$ over $B$: a scheme $D.A$ over $\operatorname{Spec} B$ with commutative relative group law $D.L$ and property bundle, together with $D.g : E_0.A \to D.A$ making $E_0.f$ a pullback of $D.f$ along $\operatorname{Spec}$ of $B \to B_0$ and compatible with the two group laws. Assume $D.f$ is smooth of relative dimension $2$, and let $W$ be an open subscheme of the kernel scheme $D.L.\mathrm{schemeKer}\,N$ (the pullback of $N$-multiplication $D.L.\mathrm{schemeNsmul}\,N$ along the unit section) whose underlying set is the preimage, under the first projection to $D.A$, of the image under $D.g$ of the set-theoretic range of $E_0.\mathrm{lev}$. The assertion is that for every scheme $C'$ and every closed immersion $\mathrm{lev}' : C' \to D.A$ such that (i) every point $P$ of $D.A$ over a morphism $t : T \to \operatorname{Spec} B$ which factors through $\mathrm{lev}'$ satisfies $N \cdot P =$ the unit point, (ii) $\mathrm{lev}'$ followed by $D.f$ is finite, flat and locally of finite presentation with fibre rank $N^2$ at every point of $\operatorname{Spec} B$, and (iii) every point of $E_0.A$ over $t' : T \to \operatorname{Spec} B_0$ factoring through $E_0.\mathrm{lev}$ has the property that $P$ followed by $D.g$ factors through $\mathrm{lev}'$, one has, for every scheme $T$, every $t : T \to \operatorname{Spec} B$ and every point $P$ of $D.A$ over $t$: $P$ factors through the inclusion of $W$ followed by the projection $D.L.\mathrm{schemeKer}\,N \to D.A$ if and only if $P$ factors through $\mathrm{lev}'$.
--
--   This is the uniqueness half of the lifting of a level structure along an infinitesimal (nilpotent, surjective) thickening $B \to B_0$ of the base: any finite flat closed subscheme of the $N$-torsion of the deformation, of rank $N^2$ and containing the level structure of the special fibre, coincides with the distinguished open piece $W$ of the kernel scheme as a functor of points. It is used by [`GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension`](thm.html#GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension), which produces the level structure on a bare deformation of a fake elliptic curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_levelPiece_unique.lean

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

theorem GoodReductionJacobian.BareDeformation.levelPiece_unique
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f]
    (W : (D.L.schemeKer N).Opens)
    (hW : (W : Set ↥(D.L.schemeKer N)) = ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base))) :
      (∀ (C' : Scheme.{0}) (lev' : C' ⟶ D.A), IsClosedImmersion lev' →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
          FactorsThrough lev' P → nsmulPt D.L t N P = D.L.one t) →
        IsFinite (lev' ≫ D.f) → Flat (lev' ≫ D.f) → LocallyOfFinitePresentation (lev' ≫ D.f) →
        (∀ s : ↥(Spec (CommRingCat.of B)), (lev' ≫ D.f).finrank s = N ^ 2) →
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
          FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ C', P₀ ≫ lev' = P.1 ≫ D.g) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
          FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) P ↔ FactorsThrough lev' P) := by sorry
