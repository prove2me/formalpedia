-- Prove2me | Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
-- name    : IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/70c9f82f-802c-556e-af0a-47cef03e74ff
-- title:
--   Residue characteristic p when p lies in the maximal ideal
-- statement:
--   Let $A$ be a commutative ring that is local in Mathlib's sense (`IsLocalRing`), so that it has a unique maximal ideal $\mathfrak m_A =$ `IsLocalRing.maximalIdeal A` and residue field $\kappa = A/\mathfrak m_A =$ `IsLocalRing.ResidueField A`, and let $p$ be a prime natural number. Assume that the image of $p$ under the canonical map $\mathbb N \to A$ lies in $\mathfrak m_A$. The conclusion is the instance-shaped assertion `CharP (IsLocalRing.ResidueField A) p`: the residue field of $A$ has characteristic $p$, i.e. for every natural number $n$, the image of $n$ in $\kappa$ vanishes if and only if $p \mid n$. No further hypotheses on $A$ are imposed; in particular $A$ is not assumed to be a domain, Noetherian or a valuation ring, and $\mathfrak m_A$ is not assumed to contain $p$ as a generator.
--
--   This is the standard computation of the residue characteristic of a local ring in which the rational prime $p$ is not a unit. It serves to discharge `CharP` hypotheses on residue fields throughout the project, for instance for models over a base such as $\mathbb Z_{(p)}[\zeta_p]$ whose special fibre carries characteristic-$p$ geometry; it is cited by many statements about special fibres of modular curves and about coset graphs in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal
    (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) p := by sorry
