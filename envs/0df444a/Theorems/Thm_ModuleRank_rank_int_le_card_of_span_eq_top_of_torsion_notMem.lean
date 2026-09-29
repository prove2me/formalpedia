-- Prove2me | Theorems.Thm_ModuleRank_rank_int_le_card_of_span_eq_top_of_torsion_notMem
-- name    : ModuleRank.rank_int_le_card_of_span_eq_top_of_torsion_notMem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T13:21:02.520038+00:00
-- url     : https://prove2.me/theorems/4b41ea56-1b81-4d9c-a8e5-b0da1117c711
-- title:
--   A module over the integers spanned by a family has rank at most the number of members that are not torsion
-- statement:
--   Let $M$ be an abelian group, regarded as a module over $\mathbb{Z}$, spanned by a
--   finite family $(a_i)$, and let $J$ be a finite set of indices such that every $a_i$ with
--   $i \notin J$ is **torsion**, that is, some nonzero integer multiple of it vanishes. Then the rank
--   of $M$, as a cardinal, is at most the cardinality of $J$.
--
--   The members outside $J$ contribute nothing: the submodule spanned by the members inside $J$ has
--   torsion quotient, so that quotient has rank zero, and rank is additive across it because
--   $\mathbb{Z}$ is a domain and so satisfies rank-nullity. No hypothesis is placed on the members
--   inside $J$ -- they need not be independent, nor of infinite order -- so the statement is an
--   inequality and not an equality.
--
--   Three further points. The rank is the cardinal-valued one, so the inequality has content even
--   when $M$ is not of finite rank; the natural-number valued `finrank` form follows in one step, and
--   is strictly weaker, since truncating an infinite rank to zero would make it say nothing exactly
--   where it matters. The set $J$ carries no minimality, no non-vanishing and no
--   non-torsion requirement: $J$ empty is admissible, and then the hypotheses force the rank to be
--   $0$; $J$ everything is admissible too, and then the torsion hypothesis is empty. And no
--   finiteness is imposed on the index type -- the family may be infinite, so long as the members
--   outside $J$ are torsion.
-- source:
--   Proved in the course of the Wolf mission (J. A. Wolf, Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421-446, https://doi.org/10.4310/jdg/1214428658); used there to identify Wolf's rank of a lower central factor with the number of members of infinite order in an adapted generating family, en route to Theorem 3.2.

import Mathlib

namespace ModuleRank

theorem rank_int_le_card_of_span_eq_top_of_torsion_notMem {ι : Type*} {M : Type*}
    [AddCommGroup M] (a : ι → M) (hspan : Submodule.span ℤ (Set.range a) = ⊤)
    (J : Finset ι) (htor : ∀ i ∉ J, ∃ n : ℤ, n ≠ 0 ∧ n • a i = 0) :
    Module.rank ℤ M ≤ (J.card : Cardinal) := by
  sorry

end ModuleRank
