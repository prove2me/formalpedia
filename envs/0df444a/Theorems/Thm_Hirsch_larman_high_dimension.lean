-- Prove2me | Theorems.Thm_Hirsch_larman_high_dimension
-- name    : Hirsch.larman_high_dimension
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:33.335079+00:00
-- url     : https://prove2.me/theorems/507c8e25-a700-4a81-b02b-19513726f53a
-- title:
--   Larman's bound in dimension at least $4$
-- statement:
--   Let $P\subseteq\mathbb{R}^d$ be a nonempty bounded H-polytope described by $n$ linear inequalities, and assume $d\ge 4$. Then the combinatorial diameter of $P$ is at most $n\cdot 2^{d-3}$:
--
--   $$
--   \operatorname{DiamLE}(P,\, n\cdot 2^{d-3}).
--   $$
--
--   This is the inductive content of Larman's theorem, after the case $d\le 3$ has been reduced to the Hirsch bound $n-d$ (already proved as the mission's dimension-three milestone). For $d\ge 4$ the exponent $d-3$ is a genuine positive power of two, and the argument proceeds by walking through facets of one lower dimension.
--
--   **Formalization Note** The hypothesis $4\le d$ is a natural-number inequality. The exponent uses truncated subtraction, so it agrees with $2^{d-3}$ in the usual integers.
-- source:
--   Larman, Paths on polytopes, Proc. London Math. Soc. s3-20 (1970) 161-178, https://doi.org/10.1112/plms/s3-20.2.249. The case d ≥ 4 of the bound n · 2^{d-3}; the mission's d ≤ 3 case is Hirsch.dimension_three_bound.

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem larman_high_dimension (d n : ℕ) (hd : 4 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) := by sorry

end Hirsch
