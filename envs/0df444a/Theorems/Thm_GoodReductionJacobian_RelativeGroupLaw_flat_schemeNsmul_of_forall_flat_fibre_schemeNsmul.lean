-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/726b9fa1-2349-5887-b4e2-e622dca97756
-- title:
--   Flatness of [n] from flatness on all fibres
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism that is flat and locally of finite presentation. Let $G$ be a relative group law on $f$ over $R$: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$, a multiplication, a unit and an inversion on the set of $t$-points $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$, satisfying associativity, both unit laws and the left inverse law, and natural in the base: for $\psi \colon T' \to T$ with $t' = \psi$ followed by $t$, composition with $\psi$ carries products to products. Let $n \in \mathbf{N}$. The morphism $[n] =$ `G.schemeNsmul n` $\colon A \to A$ is the underlying morphism of the $n$-fold power, formed by iterating $G$'s multiplication starting from the unit, of the tautological $f$-point $\mathrm{id}_A$ of $A$. For a point $s$ of the scheme $\operatorname{Spec} R$, `G.fibre s` is the induced group law on the fibre $A_s = A \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa(s)$ over the residue field $\kappa(s)$, its points being transported from points of $A$ over $\kappa(s)$-points of the base through the pullback. Assuming that for every $s$ the morphism $[n]$ of the fibre group law `G.fibre s` is flat, the conclusion is that $[n] \colon A \to A$ is flat.
--
--   This is the fibrewise criterion of flatness (critère de platitude par fibres) specialised to the $R$-endomorphism given by multiplication by $n$ on a flat, locally finitely presented scheme with a relative group law; no Noetherian hypothesis is imposed on $R$. It feeds the results establishing that multiplication by $n$ is flat, surjective and locally quasi-finite, which in turn supply the finite flat $n$-torsion used in the study of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [Flat f] [LocallyOfFinitePresentation f] (G : RelativeGroupLaw R f) (n : ℕ)
    (hfib : ∀ s : (Spec (CommRingCat.of R) : Scheme.{u}), Flat ((G.fibre s).schemeNsmul n)) :
    Flat (G.schemeNsmul n) := by sorry
