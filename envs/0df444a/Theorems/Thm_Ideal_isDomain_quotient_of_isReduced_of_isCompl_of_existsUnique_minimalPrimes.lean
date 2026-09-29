-- Prove2me | Theorems.Thm_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes
-- name    : Ideal.isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/a4c68bfc-c004-5fa8-b33e-8307296e0895
-- title:
--   Reduced ring: a complemented ideal with one minimal prime over it
-- statement:
--   Let $R$ be a reduced commutative ring and let $I,J$ be ideals of $R$ that are complements in the lattice of ideals, i.e. $I\sqcap J=\bot$ and $I\sqcup J=\top$ (equivalently $I\cap J=0$ and $I+J=R$). Assume the quotient ring $R/I$ is nontrivial, and assume there is exactly one ideal $\mathfrak p$ of $R$ that is both a minimal prime over the zero ideal (that is, $\mathfrak p\in(\bot)^{\mathrm{minimalPrimes}}$: $\mathfrak p$ is prime, contains $\bot$, and is minimal among such) and contains $I$; uniqueness is asserted in the strong form that any ideal with these two properties equals $\mathfrak p$. The conclusion is that $R/I$ is an integral domain, i.e. it is a nontrivial commutative ring without zero divisors.
--
--   This is the elementary commutative-algebra statement that a direct factor of a reduced ring lying over a single minimal prime is a domain: under complementarity the ideal $I$ is radical and coincides with the unique minimal prime above it. It is used in the analysis of a ring attached to modular curves of full level, where it supplies the domain property of a quotient by an explicitly given ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes
    (R : Type) [CommRing R] [IsReduced R] (I J : Ideal R) (hIJ : IsCompl I J)
    [Nontrivial (R ⧸ I)]
    (huniq : ∃! 𝔭 : Ideal R, 𝔭 ∈ (⊥ : Ideal R).minimalPrimes ∧ I ≤ 𝔭) :
    IsDomain (R ⧸ I) := by sorry
