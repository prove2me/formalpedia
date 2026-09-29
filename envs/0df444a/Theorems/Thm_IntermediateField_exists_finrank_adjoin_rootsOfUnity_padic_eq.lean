-- Prove2me | Theorems.Thm_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq
-- name    : IntermediateField.exists_finrank_adjoin_rootsOfUnity_padic_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/c477863b-7b11-5eab-9c21-0bf3a2b9d334
-- title:
--   Every degree is realised by a μ_{q^N-1} extension of a local field
-- statement:
--   Let $q$ be a prime and let $K$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq$ `PadicAlgCl q` (a fixed algebraic closure of $\mathbb{Q}_q$) which is finite-dimensional over $\mathbb{Q}_q$, and let $n$ be a natural number with $0 < n$. The assertion is that there exists a natural number $N$ with $0 < N$ such that the $K$-dimension of the intermediate field obtained by adjoining to $K$ the set $\{\zeta \in \mathrm{PadicAlgCl}\ q : \zeta^{q^N-1} = 1\}$ of all $(q^N-1)$-st roots of unity in the algebraic closure equals $n$; that is, $[K(\mu_{q^N-1}) : K] = n$. Thus every prescribed finite degree $n \ge 1$ occurs as the degree over $K$ of one of the extensions $K(\mu_{q^N-1})$, $N \ge 1$.
--
--   The extensions $K(\mu_{q^N-1})$ are the finite unramified layers over $K$, and the statement says that their degrees exhaust all positive integers; it is used to produce an unramified extension of prescribed degree, for instance when choosing a layer over which a Frobenius element or a uniformiser behaves as required, and in the local-level and cohomological splitting arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IntermediateField

theorem IntermediateField.exists_finrank_adjoin_rootsOfUnity_padic_eq (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (n : ℕ) (hn : 0 < n) :
    ∃ N : ℕ, 0 < N ∧
      Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) = n := by sorry
