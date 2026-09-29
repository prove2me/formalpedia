-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree
-- name    : IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/7d10be89-61c6-5796-8fd7-0761f72a2984
-- title:
--   Dedekind's criterion over a DVR: O[α] integrally closed
-- statement:
--   Let $O$ be a commutative domain that is a discrete valuation ring, let $\varpi \in O$ be an irreducible element, and let $F$ be a field equipped with an $O$-algebra structure whose structure map is injective (a faithful scalar action). Let $\alpha \in F$ be integral over $O$, so that its minimal polynomial $\operatorname{minpoly}_O(\alpha) \in O[X]$ is available, and assume two things: first, that the image of $\operatorname{minpoly}_O(\alpha)$ under the coefficientwise reduction $O \to O/(\varpi)$ is a squarefree element of $(O/(\varpi))[X]$; second, that $F$ is generated from the $O$-subalgebra $O[\alpha] =$ `Algebra.adjoin O {α}` by inverting $\varpi$ in the weak sense that for every $x \in F$ there is an $n \in \mathbb{N}$ with $\varpi^n x \in O[\alpha]$ (the power of $\varpi$ being taken in $F$ via the structure map). The conclusion is that $O[\alpha]$ is integrally closed in $F$: every element of $F$ which is integral over the subalgebra $O[\alpha]$ already lies in (the image of) $O[\alpha]$.
--
--   This is Dedekind's criterion in the local form: squarefreeness of the reduced minimal polynomial at the uniformiser suffices for the monogenic order $O[\alpha]$ to be integrally closed in the ring obtained from it by inverting $\varpi$, with no separability or irreducibility assumption and no condition on the residue field. It is the arithmetic input used when integral closedness of an explicitly generated order is needed, and it feeds into the reducedness statements for quotients by a uniformiser and for tensor products of separable algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    {α : F} (hα : IsIntegral O α)
    (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F ϖ ^ n * x ∈ Algebra.adjoin O {α}) :
    IsIntegrallyClosedIn (Algebra.adjoin O {α}) F := by sorry
