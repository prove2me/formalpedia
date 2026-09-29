-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
-- name    : IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c72b9831-0bd2-5d16-a597-66c7c5601f9d
-- title:
--   Finiteness of the residue field of 𝒪ᵥ
-- statement:
--   Let $R$ be a commutative ring which is a Dedekind domain, let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$, and let $v$ be a point of the height-one spectrum of $R$, i.e. a nonzero prime ideal `v.asIdeal` of $R$. Assume the quotient ring $R / v$ is finite. The conclusion is that the residue field of the local ring $\mathcal{O}_v =$ `v.adicCompletionIntegers K`, the valuation subring of the $v$-adic completion $K_v$ of $K$ cut out by the canonical $\mathbb{Z}$-valued (in $\mathbb{Z}_{\mathrm{m}} \cup \{0\}$, written `WithZero (Multiplicative ℤ)`) valuation on $K_v$, is finite; that is, $\mathcal{O}_v$ modulo its maximal ideal is a finite type. Finiteness here is the `Finite` predicate, not an explicit cardinality bound: no relation between $\#(R/v)$ and $\#(\mathcal{O}_v/\mathfrak{m}_v)$ is asserted, although the proof in fact exhibits the latter as a quotient of the former.
--
--   This is the standard fact that a nonarchimedean local field (or, more generally, the completion of a Dedekind domain at a finite place with finite residue ring) has finite residue field, with the residue field of the completion identified as a quotient of $R/v$. It supplies the `Finite (IsLocalRing.ResidueField …)` hypothesis needed throughout the local theory used in the project, for instance in the construction of Galois representations attached to normalised Hecke eigenforms and in the computation of Frobenius characteristic polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by sorry
