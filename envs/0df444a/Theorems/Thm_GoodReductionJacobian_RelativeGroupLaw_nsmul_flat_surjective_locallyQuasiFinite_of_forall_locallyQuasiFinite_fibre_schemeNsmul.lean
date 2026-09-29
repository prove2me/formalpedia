-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0061de68-0ace-58e1-b355-3d1770af124c
-- title:
--   Fibrewise quasi-finiteness makes [n] flat, surjective, quasi-finite
-- statement:
--   Let $R$ be a commutative ring, let $G$ be a scheme and let $g \colon G \to \operatorname{Spec} R$ be a smooth morphism. Let $L$ be a relative group law on $g$, that is, a functorial group structure on the sets $\{\varphi : T \to G \mid \varphi \circ t = g\}$ of $T$-points over each $t \colon T \to \operatorname{Spec} R$, with multiplication compatible with precomposition in $T$, and assume $L$ is commutative (all these point groups are abelian). Assume furthermore that for every point $s$ of $\operatorname{Spec} R$ the fibre $g^{-1}(\{s\})$ of the underlying continuous map is preconnected, and that for every such $s$ and every $n \ge 1$ whose image in the residue field $\kappa(s)$ of $\operatorname{Spec} R$ at $s$ is not a unit, the multiplication-by-$n$ endomorphism of the fibre $G_s = G \times_{\operatorname{Spec} R} \operatorname{Spec}\kappa(s)$ attached to the base-changed group law $L_s$ is locally quasi-finite. Then for every $n \ge 1$ the endomorphism $[n] \colon G \to G$ obtained by applying the $n$-fold multiplication of $L$ to the identity point of $G$ over $g$ is flat, surjective, and locally quasi-finite.
--
--   This is the standard statement that multiplication by $n$ on a smooth commutative group scheme with connected fibres is flat, surjective and locally quasi-finite, the fibrewise hypothesis being needed only at the residue characteristics dividing $n$. It is used to verify these properties for multiplication by $n$ on relative Jacobians and on the Néron-model-type group schemes attached to modular curves, where the $n$-torsion subscheme is then finite flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul
    {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)} [Smooth g]
    (L : RelativeGroupLaw R g) (hc : L.IsCommutative)
    (hconn : ∀ s : Spec (CommRingCat.of R), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hfib : ∀ (s : Spec (CommRingCat.of R)) (n : ℕ), 0 < n → ¬ IsUnit ((n : GoodReductionJacobian.RelativeGroupLaw.baseResidueField s)) →
      LocallyQuasiFinite ((L.fibre s).schemeNsmul n)) :
    (∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)) ∧ (∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)) ∧
      (∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n)) := by sorry
