-- Prove2me | Theorems.Thm_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim
-- name    : IsIntegrallyClosed.exists_isRegular_pair_of_two_le_ringKrullDim
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/6be1cef1-712b-5996-a70b-36b46588f197
-- title:
--   Regular pair extending a nonzero element in a normal local domain of dimension ≥ 2
-- statement:
--   Let $B$ be a commutative Noetherian local integral domain that is integrally closed in its field of fractions, and suppose its Krull dimension satisfies $2 \le \dim B$ (the inequality being taken in `WithBot ℕ∞`, so in particular $B$ is not a field). Let $t$ be an element of the maximal ideal $\mathfrak m$ of $B$ with $t \neq 0$. Then there exists $b \in \mathfrak m$ such that the two-term list $[t,b]$ is a regular sequence on $B$ as a module over itself, in the sense of `RingTheory.Sequence.IsRegular`: $t$ is a non-zerodivisor on $B$, $b$ acts as a non-zerodivisor on $B/tB$, and the final quotient $B/(t,b)$ is nonzero. The conclusion is the statement that the depth of $B$ is at least $2$ in the strong form that the regular sequence may be chosen to begin with the prescribed element $t$.
--
--   This is the elementary half of Serre's normality criterion in the form '$\mathfrak m \notin \operatorname{Ass}(B/tB)$ for a normal Noetherian local domain of dimension at least two', i.e. that such a ring satisfies $S_2$ and hence has depth $\ge 2$. It is used in the analysis of adic completions of normal local rings occurring as models of modular curves, in particular for the completion of an unramified finite extension and for the identification of such a completion with a crossing model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegrallyClosed.exists_isRegular_pair_of_two_le_ringKrullDim
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B]
    (hdim : 2 ≤ ringKrullDim B) (t : B) (ht : t ∈ IsLocalRing.maximalIdeal B) (ht0 : t ≠ 0) :
    ∃ b : B, b ∈ IsLocalRing.maximalIdeal B ∧ RingTheory.Sequence.IsRegular B [t, b] := by sorry
