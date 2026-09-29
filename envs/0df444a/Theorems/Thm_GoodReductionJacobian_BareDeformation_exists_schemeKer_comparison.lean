-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison
-- name    : GoodReductionJacobian.BareDeformation.exists_schemeKer_comparison
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/8a1d07ff-a2f2-583b-9984-c8a857d98762
-- title:
--   Torsion kernels of a bare deformation are base changes
-- statement:
--   Let $B \to S$ be a homomorphism of commutative rings (given as an algebra structure), let $A_S$ be a scheme with structure morphism $f_S : A_S \to \operatorname{Spec} S$, and let $L_S$ be a relative group law on $f_S$, that is, a functorial group structure on the sets $\{\varphi : T \to A_S \mid \varphi \circ f_S = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} S$, with multiplication natural in $T$. Let $D$ be a bare deformation of $(f_S, L_S)$ to $B$: it consists of a scheme $A$ with $f : A \to \operatorname{Spec} B$, a commutative relative group law $L$ on $f$, a bundle `AbelianSchemePropertyBundle B f` of geometric properties of $f$, a morphism $g : A_S \to A$ making the square with $f_S$, $f$ and $\operatorname{Spec}$ of $B \to S$ cartesian, and the requirement that $g$ be multiplicative on points. Let $n \in \mathbb{N}$. For a relative group law $G$, `schemeKer G n` denotes the fibre product of the morphism $[n] : A \to A$ underlying the $n$-fold sum of the tautological point with the unit section $\operatorname{Spec} R \to A$, and `schemeKerStr G n` its projection to $\operatorname{Spec} R$. The assertion is that there exists $g_K : L_S.\mathrm{schemeKer}\, n \to D.L.\mathrm{schemeKer}\, n$ such that $g_K$ followed by the first projection to $A$ equals the first projection to $A_S$ followed by $g$, and such that the square formed by $g_K$, the two structure morphisms `schemeKerStr` and $\operatorname{Spec}$ of $B \to S$ is cartesian; thus $L_S.\mathrm{schemeKer}\, n \cong (D.L.\mathrm{schemeKer}\, n) \times_{\operatorname{Spec} B} \operatorname{Spec} S$.
--
--   This is the statement that the $n$-torsion kernel of a relative group law is compatible with base change along the deformation datum: the $n$-torsion of the special fibre datum is the fibre product of the $n$-torsion over $\operatorname{Spec} B$ with $\operatorname{Spec} S$. No condition on $B \to S$ beyond the algebra structure enters. It is used in the analysis of level structures on bare deformations, in particular in the lemmas `exists_level_lift_of_smoothOfRelativeDimension`, `levelPiece_isClosedImmersion_finite_flat_finrank` and `levelPiece_unique`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_schemeKer_comparison
    {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
    {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    (D : BareDeformation fₛ Lₛ B) (n : ℕ) :
    ∃ gK : Lₛ.schemeKer n ⟶ D.L.schemeKer n,
      gK ≫ pullback.fst (D.L.schemeNsmul n) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 =
        pullback.fst (Lₛ.schemeNsmul n) (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ D.g ∧
      IsPullback gK (Lₛ.schemeKerStr n) (D.L.schemeKerStr n)
        (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by sorry
