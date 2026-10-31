-- Prove2me | Theorems.Thm_LegalAssign_lemma_4_2
-- name    : LegalAssign.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:47.249786+00:00
-- url     : https://prove2.me/theorems/836703de-a608-4c21-abb4-d03fcd2e992c
-- title:
--   Lemma 4.2 — rotation elimination preserves stability and generates all stable assignments (corrected: s_M has a vacancy clause and a rotation follows next_M)
-- statement:
--   Let $(G,<,q)$ be an instance, let $X$ be one side of the bipartition and $Y$ the other. Then:
--
--   1. if $M$ is stable and $\rho$ is an $X$-rotation exposed in $M$, then $M':=M/\rho$ is stable;
--   2. in that case $M\succ M'$ if $X$ is the set of students, and $M\prec M'$ if $X$ is the set of schools;
--   3. if no $X$-rotation is exposed in a stable assignment $M$, then $M$ is the $Y$-optimal stable assignment;
--   4. every stable assignment is obtained from the $X$-optimal stable assignment by a sequence of $X$-rotation eliminations;
--   5. any two such sequences with the same target contain the same set of $X$-rotations.
--
--   The lemma extends the classical rotation structure from stable marriage to the one-to-many setting.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - correction: s_M(x) is the first y ∉ M(x) on the list of x with x >_y x′ for some x′ ∈ M(y) → the first y ∉ M(x) with x >_y x′ for some x′ ∈ M(y) or |M(y)| < q_y; reason: as printed Lemma 4.2 is false; students x0, x1, t, schools y0, y1 of quota 1 and z of quota 2, x0: y0 > z > y1, x1: y1 > y0, t: z, y0: x1 > x0, y1: x0 > x1, z: t > x0; M = {x0y0, x1y1, tz} is stable and the printed rotation gives M/ρ = {x0y1, x1y0, tz}, blocked by x0z
--   - correction: a cycle y_0, x_0, …, y_{r-1}, x_{r-1} is a rotation exposed in M if x_i y_i ∈ M and s_M(x_i) = y_{i+1} → also next_M(x_i) = x_{i+1}, as in the directed cycles of D_X that the source identifies with rotations; reason: as printed Lemma 4.2 is false for quotas ≥ 2; students x0, x1, w0, w1, schools y0, y1 of quota 2, x0: y0 > y1, x1: y1 > y0, w0: y0, w1: y1, y0: x0 > x1 > w0, y1: x1 > x0 > w1; M = {x0y0, w0y0, x1y1, w1y1} is stable and M/ρ = {x0y1, w0y0, x1y0, w1y1} is blocked by x0y0
--   - reading: M′(x_i) = (M′(x_i) \ {y_i}) ∪ {y_{i+1}} → M/ρ = (M \ {x_i y_i}) ∪ {x_i y_{i+1}}; reason: the printed formula defines M′ by itself, a typo for M(x_i) on the right
--   - reading: every such sequence contains the same set of X-rotations → any two elimination sequences from the X-optimal stable assignment to the same stable assignment M; reason: sequences to different targets plainly differ
--   - encoding: a rotation is a cycle of G → Rotation with x, y : Fin (n+1) → _ injective, compared through Rotation.key, the pair of sets {(x_i, y_i)} and {(x_i, y_{i+1})}; reason: a cyclic shift of the indices is the same rotation
--   - encoding: the X-optimal and Y-optimal stable assignments (existence is Theorem 4.1, not in this mission) → hypotheses IsStudentOptimal or IsSchoolOptimal on a bound variable; reason: the lemma is about those assignments; existence is not its content
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma 4.2, p.9 (cited from Bansal et al. [7]); definitions p.9

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_Rotation

namespace LegalAssign

/-- Lemma 4.2 (arXiv:1809.08506v2, p.9, cited from Bansal et al. [7]), for both choices of `X`.
For `M` stable and `ρ` an `X`-rotation exposed in `M`, `M/ρ` is stable, with `M ≻ M/ρ` for
`X` = students and `M/ρ ≻ M` for `X` = schools. If no `X`-rotation is exposed in a stable `M`, then
`M` is `Y`-optimal. Every stable assignment is reached from the `X`-optimal one by eliminations, and
any two such sequences with the same target contain the same set of rotations.

**Formalization Note** Rotations are the corrected ones of `Side.IsExposed`. "Every such sequence" is
read as every sequence to the same target; rotations are compared through `Rotation.key`. -/
theorem lemma_4_2 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    ((∀ M ∈ G.stable, ∀ ρ, G.studentSide.IsExposed M ρ →
        G.studentSide.eliminate M ρ ∈ G.stable ∧
          G.StrictlyDominates M (G.studentSide.eliminate M ρ)) ∧
      (∀ M ∈ G.stable, (¬ ∃ ρ, G.studentSide.IsExposed M ρ) → G.IsSchoolOptimal M) ∧
      (∀ M₀, G.IsStudentOptimal M₀ → ∀ M ∈ G.stable, ∃ l, G.studentSide.IsEliminationPath M₀ l M) ∧
      (∀ M₀, G.IsStudentOptimal M₀ → ∀ M ∈ G.stable, ∀ l l',
        G.studentSide.IsEliminationPath M₀ l M → G.studentSide.IsEliminationPath M₀ l' M →
          rotationKeys l = rotationKeys l')) ∧
    ((∀ M ∈ G.stable, ∀ ρ, G.schoolSide.IsExposed M ρ →
        G.schoolSide.eliminate M ρ ∈ G.stable ∧
          G.StrictlyDominates (G.schoolSide.eliminate M ρ) M) ∧
      (∀ M ∈ G.stable, (¬ ∃ ρ, G.schoolSide.IsExposed M ρ) → G.IsStudentOptimal M) ∧
      (∀ Mz, G.IsSchoolOptimal Mz → ∀ M ∈ G.stable, ∃ l, G.schoolSide.IsEliminationPath Mz l M) ∧
      (∀ Mz, G.IsSchoolOptimal Mz → ∀ M ∈ G.stable, ∀ l l',
        G.schoolSide.IsEliminationPath Mz l M → G.schoolSide.IsEliminationPath Mz l' M →
          rotationKeys l = rotationKeys l')) := by sorry

end LegalAssign
