-- Prove2me | Theorems.Thm_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf
-- name    : GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/66f3e5b4-68a7-5414-a070-16a38c1aa2ac
-- title:
--   Generic fibre of a finite flat Hopf algebra over ℤ_{(q)} splits
-- statement:
--   Let $q$ be a prime and let $R =$ [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $q$ (the localisation $\mathbb{Z}_{(q)}$). Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$, finite and flat as an $R$-module, and with cocommutative comultiplication. Let $P$ denote the type `WithConv` applied to the $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, a copy of that set of $\overline{\mathbb{Q}}$-points of $\operatorname{Spec} H$, with `WithConv.ofConv` recovering from $\nu \in P$ the corresponding algebra homomorphism. The assertion is that the $\overline{\mathbb{Q}}$-algebra homomorphism
--   $$\overline{\mathbb{Q}} \otimes_{R} H \longrightarrow (P \to \overline{\mathbb{Q}}), \qquad t \otimes h \longmapsto \big(\nu \mapsto t\,\nu(h)\big),$$
--   obtained by lifting the structure map $\overline{\mathbb{Q}} \to (P \to \overline{\mathbb{Q}})$ and the map $H \to (P \to \overline{\mathbb{Q}})$ with components the $\nu$ (their images commute, the target being commutative), is bijective as a function.
--
--   This is the statement that the generic fibre of a finite flat commutative group scheme over $\mathbb{Z}_{(q)}$ is étale and becomes constant over $\overline{\mathbb{Q}}$, in the form of an algebra isomorphism $\overline{\mathbb{Q}} \otimes_{\mathbb{Z}_{(q)}} H \cong \overline{\mathbb{Q}}^{P}$. It supports the analysis of multiplicative-type pieces and reduction kernels along admissible chains, and the construction of models whose generic-fibre points are prescribed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H] :
    Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom (GaloisRep.ratLocalizedAt q) _
          fun ν : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) => (WithConv.ofConv ν : H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[AlgebraicClosure ℚ] (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) := by sorry
