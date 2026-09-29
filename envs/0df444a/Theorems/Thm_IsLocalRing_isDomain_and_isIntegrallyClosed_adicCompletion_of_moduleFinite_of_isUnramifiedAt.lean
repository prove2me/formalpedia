-- Prove2me | Theorems.Thm_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt
-- name    : IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/8bc0c102-3694-5527-8ad5-4d6f6d2a1ed6
-- title:
--   Analytic normality of a normal two-dimensional local domain
-- statement:
--   Let $R_0$ be a Noetherian local integral domain that is integrally closed, with $\operatorname{ringKrullDim} R_0 \le 2$ in $\mathrm{WithBot}\,\mathbb{N}_\infty$, and let $S$ be a Noetherian local integral domain that is integrally closed, with $\operatorname{ringKrullDim} S \le 2$ and $2 \le \operatorname{ringKrullDim} S$ (so $S$ has Krull dimension exactly $2$). Let $t$ be an element of the maximal ideal of $S$ with $t \neq 0$. Write $\widehat S =$ `AdicCompletion (IsLocalRing.maximalIdeal S) S` for the completion of $S$ along its maximal ideal, and suppose $\widehat S$ is equipped with an $R_0$-algebra structure for which it is finite as an $R_0$-module and for which the $R_0$-action on $\widehat S$ is faithful. Assume moreover that for every prime ideal $\mathfrak{P}$ of $\widehat S$ that is not maximal, $\widehat S$ is unramified over $R_0$ at $\mathfrak{P}$, i.e. `Algebra.IsUnramifiedAt R₀ 𝔓` holds. The conclusion is that $\widehat S$ is an integral domain and is integrally closed.
--
--   This is the analytic normality statement for a two-dimensional normal local domain in the form needed later: normality of the maximal-adic completion is deduced from Serre's criterion, using regularity of $\widehat S$ at non-maximal primes (supplied by the unramifiedness hypothesis over the normal base $R_0$ of dimension at most $2$) together with a regular pair $(t,b)$ in the maximal ideal. It is used in the construction of the two-chart integral model of the modular curve $X_0(p)$-type data, where normality of a completed local ring of the model must be known.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] [IsIntegrallyClosed R₀]
    (hdimR : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] [IsIntegrallyClosed S]
    (hdimS : ringKrullDim S ≤ (2 : WithBot ℕ∞)) (hdimS' : 2 ≤ ringKrullDim S)
    (t : S) (ht : t ∈ IsLocalRing.maximalIdeal S) (ht0 : t ≠ 0)
    [Algebra R₀ (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    [Module.Finite R₀ (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    [FaithfulSMul R₀ (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    (hunr : ∀ (𝔓 : Ideal (AdicCompletion (IsLocalRing.maximalIdeal S) S)) [𝔓.IsPrime], ¬ 𝔓.IsMaximal →
      Algebra.IsUnramifiedAt R₀ 𝔓) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by sorry
