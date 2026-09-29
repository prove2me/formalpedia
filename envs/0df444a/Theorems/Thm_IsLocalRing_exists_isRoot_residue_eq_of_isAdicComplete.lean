-- Prove2me | Theorems.Thm_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete
-- name    : IsLocalRing.exists_isRoot_residue_eq_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/3b5ae8f6-0f9c-5a53-9d2e-9ae77d1c0b81
-- title:
--   Simple roots of the reduction lift in complete local rings
-- statement:
--   Let $C$ be a commutative ring which is local and complete and separated for the adic filtration given by its maximal ideal (an `IsAdicComplete (maximalIdeal C) C` instance, which in particular includes Hausdorffness of that filtration). Let $p \in C[X]$ be a monic polynomial, and let $\alpha$ be an element of the residue field $\kappa = C/\mathfrak{m}_C$. Assume that $\alpha$ is a root of the reduction of $p$, that is, of the image $\bar p$ of $p$ under the coefficientwise map induced by the residue homomorphism $\mathrm{residue}\ C : C \to \kappa$, and assume that $\alpha$ is not a root of the formal derivative of $\bar p$, i.e. $\bar p'(\alpha) \neq 0$, so that $\alpha$ is a simple root of $\bar p$. The conclusion is that there exists $x \in C$ with $p(x) = 0$ and with residue class $\mathrm{residue}\ C\, x = \alpha$; thus every simple root of the reduction of a monic polynomial lifts to an honest root in $C$ reducing to it.
--
--   This is Hensel's lemma in the form 'complete local rings are Henselian', stated for a simple root of the reduction of a monic polynomial. It is used in the verification of an étale-by-numbers criterion, [`IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete`](thm.html#IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete), where a model algebra $C[X]/(p)$ must be mapped into a complete local ring whose residue field carries a simple root of $\bar p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing in

theorem IsLocalRing.exists_isRoot_residue_eq_of_isAdicComplete
    {C : Type*} [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    (p : C[X]) (hp : p.Monic) (α : ResidueField C)
    (hα : (p.map (residue C)).IsRoot α) (hα' : ¬ (derivative (p.map (residue C))).IsRoot α) :
    ∃ x : C, p.IsRoot x ∧ residue C x = α := by sorry
