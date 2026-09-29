-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_isClopen_levelPiece
-- name    : GoodReductionJacobian.BareDeformation.isClopen_levelPiece
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/93127f59-7a9e-50c3-9618-ec91eae64069
-- title:
--   Clopenness of the level locus in the N-torsion subscheme
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B$ be a commutative local Artinian ring and $B_0$ a commutative $B$-algebra such that the structure map $B \to B_0$ is surjective with nilpotent kernel ideal, and suppose $N$ is a unit in $B$. Let $E_0$ be a fake elliptic curve over $B_0$ of type $(\Lambda,N)$ — a scheme $E_0.A$ over $\operatorname{Spec} B_0$ carrying a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ with the prescribed multiplicativity and trace conditions, and a level morphism $E_0.\mathrm{lev} : E_0.C \to E_0.A$ — and let $D$ be a bare deformation of $(E_0.f, E_0.L)$ to $B$: a scheme $D.A$ over $\operatorname{Spec} B$ with a commutative relative group law $D.L$ and property bundle, together with $D.g : E_0.A \to D.A$ making a pullback square over $\operatorname{Spec}(B \to B_0)$ and compatible with the two group laws; $D.f$ is smooth of relative dimension $2$. Write $\kappa$ for the first projection of the fibre product of the multiplication-by-$N$ endomorphism $D.L.\mathrm{schemeNsmul}\,N$ of $D.A$ (the $N$-fold group-law power of the identity point) with the unit section $\operatorname{Spec} B \to D.A$, so that its source is the $N$-torsion subscheme of $D.A$. The conclusion is that the preimage under the underlying continuous map of $\kappa$ of the image under $|D.g|$ of the range of $|E_0.\mathrm{lev}|$ is open and closed. The proof uses neither the local Artinian hypotheses on $B$ nor the smoothness of $D.f$ of relative dimension $2$.
--
--   This is the topological input for lifting a level structure across a nilpotent thickening: the locus in the $N$-torsion of the deformed group scheme that meets the level subscheme of the special fibre is shown to be a connected-component-style clopen piece. It is used by [`GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension`](thm.html#GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_isClopen_levelPiece.lean

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

theorem GoodReductionJacobian.BareDeformation.isClopen_levelPiece
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f] :
    IsClopen ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base)) := by sorry
