-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_levelPiece_isClosedImmersion_finite_flat_finrank
-- name    : GoodReductionJacobian.BareDeformation.levelPiece_isClosedImmersion_finite_flat_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/e23ae911-7a15-5eb2-98b9-124a671d3a4f
-- title:
--   Lifted level piece: closed immersion, finite flat of rank N²
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B$ be a local artinian commutative ring and $B_0$ a commutative $B$-algebra such that the structure map $B \to B_0$ is surjective with nilpotent kernel, and assume $N$ is invertible in $B$. Let $E_0$ be a fake elliptic curve of level $N$ over $B_0$ for $\Lambda$ (a scheme $E_0.A$ over $\operatorname{Spec} B_0$ carrying a commutative relative group law $E_0.L$, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action compatible with the group law and subject to a trace condition, together with level data including a morphism `E₀.lev` from $E_0.C$ to $E_0.A$), and let $D$ be a bare deformation of $(E_0.f, E_0.L)$ to $B$: a scheme $D.A$ over $\operatorname{Spec} B$ with commutative relative group law $D.L$ and abelian-scheme property bundle, together with a morphism $D.g : E_0.A \to D.A$ making the square over $\operatorname{Spec}(B_0) \to \operatorname{Spec}(B)$ cartesian and compatible with the two group laws; assume $D.f$ is smooth of relative dimension $2$. Let $W$ be an open subscheme of $D.L$'s $N$-torsion scheme `D.L.schemeKer N`, the pullback of the $N$-fold multiplication morphism `D.L.schemeNsmul N` along the unit section, and assume that the underlying set of $W$ is exactly the preimage, under the base map of the first projection `pullback.fst`, of the image under $D.g$ of the set-theoretic range of `E₀.lev`. Write $j$ for the composite of the open immersion $W \hookrightarrow$ `D.L.schemeKer N` with that first projection, a morphism $W \to D.A$. Then $j$ is a closed immersion, the composite of $j$ with $D.f$ is finite, flat and locally of finite presentation, and at every point $s$ of $\operatorname{Spec} B$ the rank of this composite equals $N^2$.
--
--   This identifies the locus in the $N$-torsion of a bare deformation lying over the level structure of the fake elliptic curve in the special fibre as a finite flat closed subscheme of rank $N^2$ over the base, the shape required of a level-$N$ structure. It is used in the construction of a lift of the level structure to the deformation and in the proof that such a lift is unique.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_levelPiece_isClosedImmersion_finite_flat_finrank.lean

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

theorem GoodReductionJacobian.BareDeformation.levelPiece_isClosedImmersion_finite_flat_finrank
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f]
    (W : (D.L.schemeKer N).Opens)
    (hW : (W : Set ↥(D.L.schemeKer N)) = ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base))) :
      IsClosedImmersion (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) ∧
      IsFinite ((W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) ≫ D.f) ∧ Flat ((W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) ≫ D.f) ∧ LocallyOfFinitePresentation ((W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) ≫ D.f) ∧
      (∀ s : ↥(Spec (CommRingCat.of B)), ((W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) ≫ D.f).finrank s = N ^ 2) := by sorry
