-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_rank_coordinates
-- name    : IntervalMaxCutEPTAS.Scheme.rank_coordinates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:59.503732+00:00
-- url     : https://prove2.me/theorems/c843795d-2c7e-4d55-afba-bd601eb91b61
-- title:
--   §4.1 — rank coordinates represent the same graph
-- statement:
--   Let $I$ be an interval representation of a graph $G$ on $n$ vertices. Sort the $2n$ endpoints, placing among equal values every left endpoint before every right endpoint and breaking remaining ties arbitrarily, and replace each endpoint by its position. Then:
--
--   1. such an order exists;
--   2. for every such order and all vertices $u,v$ (possibly equal), $\ell_u\le r_v$ holds before the replacement exactly when it holds after it;
--   3. the positions form a rank representation (the endpoints are the distinct integers $1,\dots,2n$ and $\ell_v<r_v$) whose graph is $G$.
--
--   This lets §4 work with integer coordinates $1,\dots,2n$ without loss.
--
--   Differences from the source:
--   - generalization: interval endpoints are real numbers → endpoints in an arbitrary linearly ordered type R; reason: the statement only uses comparisons of endpoints; taking R = ℝ gives the source statement
--   - reading: “Sort the 2n endpoints …” (a sorting step) → existence of an admissible order stated as a conjunct; reason: the text performs this sort; stating that it can be performed is the implicit claim of the sentence
--   - encoding: replacing each endpoint by its position → a position map on Fin n ⊕ Fin n and a RankRep with the same endpoint map; reason: the same data; every admissible tie-break is quantified, not a canonical one
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §4.1 (Rank coordinates), PDF p. 15 (printed p. 14)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- §4.1: an admissible sorted order exists; for every admissible order (left before right at equal
values, other ties arbitrary) each left–right comparison `l_u ≤ r_v` keeps its truth value, and the
positions form a rank representation (distinct values `1, …, 2n`, `l_v < r_v`) of the same graph. -/
theorem rank_coordinates {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) :
    (∃ pos, AdmissibleOrder I pos) ∧
    ∀ pos, AdmissibleOrder I pos →
      (∀ u v, I.l u ≤ I.r v ↔ pos (Sum.inl u) ≤ pos (Sum.inr v)) ∧
      ∃ ρ : RankRep n, ρ.ends = pos ∧ ρ.graph = I.graph := by sorry

end IntervalMaxCutEPTAS.Scheme
