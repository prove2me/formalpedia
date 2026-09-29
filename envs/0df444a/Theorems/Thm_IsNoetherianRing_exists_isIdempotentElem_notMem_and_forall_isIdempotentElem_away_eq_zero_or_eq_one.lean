-- Prove2me | Theorems.Thm_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one
-- name    : IsNoetherianRing.exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/359e04e5-5cca-5528-a603-52b9f763fe02
-- title:
--   Idempotent localisation with no nontrivial idempotents at a prime
-- statement:
--   Let $B$ be a commutative Noetherian ring and let $\mathfrak p$ be a prime ideal of $B$. Then there exists an element $e \in B$ with the following three properties: $e$ is idempotent, $e \cdot e = e$; $e \notin \mathfrak p$; and every idempotent element of the localisation of $B$ away from $e$, i.e. of `Localization.Away e` (the localisation at the multiplicative submonoid of powers of $e$, written $B[1/e]$), equals $0$ or $1$. In other words, each prime of a Noetherian ring lies in a basic open set $D(e)$ cut out by an idempotent $e$ whose associated localisation $B[1/e]$ has only the two trivial idempotents; no claim of uniqueness of $e$ is made, and $0 = 1$ is not excluded, so the degenerate case where $B[1/e]$ is the zero ring is permitted by the disjunction.
--
--   This is the standard fact that the spectrum of a Noetherian ring is a finite disjoint union of connected clopen pieces, each of the form $D(e)$ for an idempotent $e$, together with the translation of connectedness of $\operatorname{Spec} B[1/e]$ into the absence of nontrivial idempotents in $B[1/e]$. It is used in the Čerednik–Drinfel'd part of the development, where local statements about families over a fine moduli problem are proved after passing to a connected affine neighbourhood of a given prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsNoetherianRing.exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one
    (B : Type) [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔭 ∧
      ∀ x : Localization.Away e, IsIdempotentElem x → x = 0 ∨ x = 1 := by sorry
