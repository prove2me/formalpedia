-- Prove2me | Theorems.Thm_IsIntegrallyClosed_localization_atPrime_of_adicCompletion
-- name    : IsIntegrallyClosed.localization_atPrime_of_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/579fa91c-d029-5417-b70a-d59a54b12f46
-- title:
--   Normality descends from the 𝔪-adic completion
-- statement:
--   Let $R$ be a commutative ring that is a noetherian integral domain, and let $\mathfrak m \subseteq R$ be a maximal ideal. Assume that the $\mathfrak m$-adic completion `AdicCompletion 𝔪 R`, formed as in Mathlib, is itself an integral domain and is integrally closed in its field of fractions, in the sense of Mathlib's `IsIntegrallyClosed`: every element of the fraction field of $\widehat{R}$ that is a root of a monic polynomial with coefficients in $\widehat{R}$ already lies in the image of $\widehat{R}$. The conclusion is that the localisation of $R$ at the prime $\mathfrak m$, i.e. `Localization.AtPrime 𝔪` $= R_{\mathfrak m}$, is integrally closed in the same sense: every element of its fraction field integral over $R_{\mathfrak m}$ lies in $R_{\mathfrak m}$. Thus normality of the completion is transferred to the local ring at $\mathfrak m$; note that the hypothesis is imposed on the completion and the conclusion concerns the localisation, not $R$ itself.
--
--   This is the easy direction of descent of normality along the faithfully flat map $R_{\mathfrak m} \to \widehat{R}$ for a noetherian local situation. It is used by [`Ideal.isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion`](thm.html#Ideal.isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion) to deduce normality of local rings from information about their completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_localization_atPrime_of_adicCompletion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsIntegrallyClosed.localization_atPrime_of_adicCompletion
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] (𝔪 : Ideal R) [𝔪.IsMaximal]
    [IsDomain (AdicCompletion 𝔪 R)] [IsIntegrallyClosed (AdicCompletion 𝔪 R)] :
    IsIntegrallyClosed (Localization.AtPrime 𝔪) := by sorry
