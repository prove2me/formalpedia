-- Prove2me | Theorems.Thm_IntermediateField_adjoin_rootsOfUnity_padic_mono
-- name    : IntermediateField.adjoin_rootsOfUnity_padic_mono
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/44235ecc-cf68-50ce-956e-fe2dd43c5442
-- title:
--   Monotonicity of K(μ_{q^N-1}) along divisibility
-- statement:
--   Let $q$ be a natural number carrying the hypothesis that it is prime, and let $\mathrm{PadicAlgCl}\,q$ be the algebraic closure of $\mathbb{Q}_q$ used throughout. Let $K$ be an intermediate field of the extension $\mathrm{PadicAlgCl}\,q/\mathbb{Q}_q$, and let $N, N'$ be natural numbers with $N \mid N'$. The assertion is an inclusion of intermediate fields of $\mathrm{PadicAlgCl}\,q$ over $K$: the field obtained by adjoining to $K$ the set $\{\zeta \in \mathrm{PadicAlgCl}\,q \mid \zeta^{q^N-1} = 1\}$ of roots of unity of order dividing $q^N-1$ is contained in the field obtained by adjoining to $K$ the set $\{\zeta \in \mathrm{PadicAlgCl}\,q \mid \zeta^{q^{N'}-1} = 1\}$. Here the exponents $q^N-1$ and $q^{N'}-1$ are truncated subtraction of natural numbers; in the degenerate case $N = 0$ divisibility forces $N' = 0$, so both sets are the whole field and the inclusion is trivial. In short, the tower of layers $K(\mu_{q^N-1})$ is monotone for the divisibility order on $N$.
--
--   The fields $K(\mu_{q^N-1})$ are the layers obtained by adjoining the $(q^N-1)$-st roots of unity, i.e. the unramified-type layers over $K$ inside $\overline{\mathbb{Q}}_q$, and this records that they increase along divisibility of $N$. It is used by [`groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic`](thm.html#groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic) to pass from one layer of the tower to a larger one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_adjoin_rootsOfUnity_padic_mono.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IntermediateField

theorem IntermediateField.adjoin_rootsOfUnity_padic_mono (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) {N N' : ℕ} (h : N ∣ N') :
    IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤
      IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1} := by sorry
