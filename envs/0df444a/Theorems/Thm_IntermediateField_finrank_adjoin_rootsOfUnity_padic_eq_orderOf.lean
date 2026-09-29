-- Prove2me | Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
-- name    : IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/9f3d454b-4521-5e0c-a5c6-9ebbca4c38aa
-- title:
--   Degree of K(μ_{q^N-1})/K as order of #κ
-- statement:
--   Let $q$ be a prime, let $K$ be an intermediate field of $\mathbb{Q}_q$ inside the algebraic closure `PadicAlgCl q` which is finite-dimensional over $\mathbb{Q}_q$, and let $N$ be a natural number with $0 < N$. Write $\mathcal{O}_K$ for the valuation subring `Rw q K` of $K$, namely the preimage under the structure map $K \to$ `PadicAlgCl q` of the valuation subring [`padicIntegers q`](def/GaloisRep_CompletionBridge.html#L20) attached to the valuation of `PadicAlgCl q`, and let $Q$ be the cardinality (as a `Nat.card`) of the residue field of this local ring. The assertion is that the $K$-dimension of the intermediate field obtained by adjoining to $K$ the set of all $\zeta$ in `PadicAlgCl q` with $\zeta^{q^N-1} = 1$ equals the order of the image of $Q$ in the monoid $\mathbb{Z}/(q^N-1)$ under multiplication, i.e. the multiplicative order of the residue-field cardinality modulo $q^N - 1$.
--
--   This is the standard computation of the degree of the unramified layer $K(\mu_{q^N-1})/K$ over a finite extension $K$ of $\mathbb{Q}_q$: the degree is the multiplicative order of the residue cardinality modulo $q^N-1$. It is used in the construction of Frobenius elements and uniformisers at the auxiliary local levels, and is cited by the existence statements for unramified layers with prescribed Frobenius and uniformiser data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel

theorem IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
      = orderOf ((Nat.card (IsLocalRing.ResidueField (Rw q K)) : ZMod (q ^ N - 1))) := by sorry
