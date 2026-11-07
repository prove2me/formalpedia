-- Prove2me | Theorems.Thm_IterRoundDet_lemma_2_6
-- name    : IterRoundDet.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:23.495945+00:00
-- url     : https://prove2.me/theorems/90532c99-0150-4449-92a1-2fe22bbec7bd
-- title:
--   Lemma 2.6 — the tangent space of a matroid face is described by a partition of $A$ into blocks of size $\ge 2$
-- statement:
--   Let $Q$ be a nonempty face of a matroid base polytope, let $x\in\operatorname{relint}Q$, and set $A=\{i:0<x_i<1\}$. There is a partition $A=A_1\sqcup\dots\sqcup A_q$ with $|A_j|\ge 2$ for every $j$, and hence $q\le|A|/2$, such that
--
--   $$T_Q=\{v:v_i=0\ (i\notin A),\ v(A_j)=0\ (1\le j\le q)\}.$$
--
--   The blocks are the components in which the walk exchanges mass.
--
--   Differences from the source:
--   - encoding: Q a nonempty face, x ∈ relint Q → x ∈ P(M), with T_Q as tangentAt (basePolytope M) x; reason: every x ∈ P(M) lies in the relative interior of exactly one face, its minimal face, and the two descriptions of T_Q agree
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 2.6, p.9; proof p.35

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 2.6, p.9. Let `Q` be a nonempty face of a matroid base polytope, `x ∈ relint Q`, and
`A = {i : 0 < x_i < 1}`. There is a partition `A = A_1 ∪ ⋯ ∪ A_q` with `|A_j| ≥ 2` for every `j`, and hence `q ≤ |A|/2`,
such that `T_Q = {v : v_i = 0 (i ∉ A), v(A_j) = 0 (1 ≤ j ≤ q)}`.

**Formalization Note.** "`Q` a nonempty face, `x ∈ relint Q`" is exactly "`x ∈ P(M)` and `Q` its minimal face", so
the theorem ranges over `x ∈ P(M)` and `T_Q` is `tangentAt (basePolytope M) x`. -/
theorem lemma_2_6 {n : ℕ} {M : Matroid (Fin n)} (hM : M.E = Set.univ) {x : Fin n → ℝ}
    (hx : x ∈ basePolytope M) :
    ∃ π : Finpartition (fractional x), IsFacePartition M x π ∧ (∀ s ∈ π.parts, 2 ≤ s.card) ∧
      2 * π.parts.card ≤ (fractional x).card := by sorry

end IterRoundDet
