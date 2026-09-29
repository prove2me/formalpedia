-- Prove2me | Theorems.Thm_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
-- name    : IsLocalRing.isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/38058ff1-a23e-5942-81e4-79ced40a2a02
-- title:
--   Analytic irreducibility of a DVR branch in the completion
-- statement:
--   Let $R$ be a commutative Noetherian local ring, let $\mathfrak m$ denote its maximal ideal, and write $\hat R =$ `AdicCompletion (maximalIdeal R) R` for the $\mathfrak m$-adic completion, with structure map $\iota \colon R \to \hat R$ the algebra map. Let $Q \subseteq R$ be a prime ideal such that the quotient $R/Q$ is a domain which is a discrete valuation ring. The conclusion is the conjunction of two assertions about the extended ideal $Q\hat R = \iota_*(Q)$, the image ideal of $Q$ under $\iota$: first, that $Q\hat R$ is a prime ideal of $\hat R$; and second, that for every prime ideal $P$ of $\hat R$ with $Q\hat R \subseteq P$ and $P$ not maximal, one has $P = Q\hat R$. Thus the branch of $\operatorname{Spec} R$ cut out by $Q$ remains irreducible after completion, and $Q\hat R$ is the unique non-maximal prime of $\hat R$ containing it.
--
--   This is the standard analytic irreducibility statement for a regular one-dimensional branch through the closed point of a Noetherian local ring: $\hat R / Q\hat R$ is the completion of the discrete valuation ring $R/Q$, hence again a discrete valuation ring, whose only primes are zero and the maximal ideal. It is used in the study of the two-chart integral model of the modular curve, where $R$ is the local ring at a supersingular point and $Q$ the prime of a component through it, to separate distinct branch primes of the completed local ring by their contractions to $R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (Q : Ideal R) [Q.IsPrime] [IsDomain (R ⧸ Q)] [IsDiscreteValuationRing (R ⧸ Q)] :
    (Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).IsPrime ∧
    ∀ P : Ideal (AdicCompletion (maximalIdeal R) R), P.IsPrime →
      Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤ P → ¬ P.IsMaximal →
      P = Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by sorry
