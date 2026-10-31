-- Prove2me | Theorems.Thm_LegalAssign_lemma_4_3
-- name    : LegalAssign.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:08.64872+00:00
-- url     : https://prove2.me/theorems/1bb1b21c-9185-44c2-b2b8-bb70d99d0d1b
-- title:
--   Lemma 4.3 — stable pairs are the Y-optimal pairs and the pairs of X-rotations (rotations as defined for Lemma 4.2, with the vacancy and next_M clauses)
-- statement:
--   Let $(G,<,q)$ be an instance, $X$ one side of the bipartition and $Y$ the other. An edge $xy\in E$ is a stable pair if and only if $x$ is assigned to $y$ in the $Y$-optimal stable assignment, or there are an $X$-rotation $y_0,x_0,y_1,x_1,\dots,y_{r-1},x_{r-1}$ exposed in some stable assignment and an index $i$ with
--   $$x=x_i,\qquad y=y_i.$$
--
--   The lemma lists the stable pairs of an instance through its rotations and an extreme stable assignment.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - reading: s_M(x) is the first y ∉ M(x) on the list of x with x >_y x′ for some x′ ∈ M(y) → the first y ∉ M(x) with x >_y x′ for some x′ ∈ M(y) or |M(y)| < q_y; reason: the source's own case next_M(x) = ∅ for |M(y)| < q_y presupposes the vacancy clause, and without it Lemma 4.2 is false (counterexample in that item); for Lemma 4.3 the clause only removes rotations (none can pass through a y with a free seat, since next_M(x_i) = x_{i+1} needs |M(y)| = q_y, and at a full y the two definitions of s_M agree), so the → direction is the stronger reading and ← holds under either definition because x_i y_i ∈ M with M stable
--   - reading: a cycle y_0, x_0, …, y_{r-1}, x_{r-1} is a rotation exposed in M if x_i y_i ∈ M and s_M(x_i) = y_{i+1} → also next_M(x_i) = x_{i+1}, as in the directed cycles of D_X that the source identifies with rotations; reason: the source identifies X-rotations exposed in M with the directed cycles of D_X, whose arcs use next_M, and the displayed condition alone makes Lemma 4.2 false (counterexample in that item); for Lemma 4.3 the extra clause only removes rotations, so the Lean statement implies the one with the displayed condition alone
--   - encoding: a rotation is a cycle of G → Rotation with x, y : Fin (n+1) → _ injective, indices modulo r = n + 1; reason: Lean encoding of the cycle; the same rotations
--   - encoding: the X-optimal and Y-optimal stable assignments (existence is Theorem 4.1, not in this mission) → hypotheses IsStudentOptimal or IsSchoolOptimal on a bound variable; reason: the lemma is about those assignments; existence is not its content
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma 4.3, p.9 (cited from Bansal et al. [7]); definitions p.9

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_Rotation

namespace LegalAssign

/-- Lemma 4.3 (arXiv:1809.08506v2, p.9, cited from Bansal et al. [7]), for both choices of `X`:
`xy ∈ E` is a stable pair iff `x` is assigned to `y` in the `Y`-optimal stable assignment or
`(x, y) = (x_i, y_i)` for some `X`-rotation exposed in some stable assignment.

**Formalization Note** Rotations are the corrected ones of `Side.IsExposed`. -/
theorem lemma_4_3 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    (∀ Mz, G.IsSchoolOptimal Mz → ∀ a b, (a, b) ∈ G.E →
      (G.IsStablePair a b ↔ (a, b) ∈ Mz ∨
        ∃ M ∈ G.stable, ∃ ρ, G.studentSide.IsExposed M ρ ∧ ∃ i, a = ρ.x i ∧ b = ρ.y i)) ∧
    (∀ M₀, G.IsStudentOptimal M₀ → ∀ a b, (a, b) ∈ G.E →
      (G.IsStablePair a b ↔ (a, b) ∈ M₀ ∨
        ∃ M ∈ G.stable, ∃ ρ, G.schoolSide.IsExposed M ρ ∧ ∃ i, b = ρ.x i ∧ a = ρ.y i)) := by sorry

end LegalAssign
