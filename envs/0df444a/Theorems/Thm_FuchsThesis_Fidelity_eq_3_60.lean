-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_60
-- name    : FuchsThesis.Fidelity.eq_3_60
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:48.479294+00:00
-- url     : https://prove2.me/theorems/7d3d731b-1e7c-41c8-ba7c-a006ecf0d59c
-- title:
--   Eqs. (3.60)–(3.61) — $\max_{\hat U}|\mathrm{tr}(\hat U\hat A)| = \max_{\hat U}\mathrm{Re}\,\mathrm{tr}(\hat U\hat A) = \mathrm{tr}\sqrt{\hat A^\dagger\hat A}$
-- statement:
--   Let $\hat A$ be any operator on a finite-dimensional space. Over all unitary operators $\hat U$,
--
--   $$
--   \max_{\hat U}\bigl|\mathrm{tr}(\hat U\hat A)\bigr| \;=\; \max_{\hat U}\mathrm{Re}\bigl[\mathrm{tr}(\hat U\hat A)\bigr] \;=\; \mathrm{tr}\sqrt{\hat A^\dagger\hat A} .
--   $$
--
--   Moreover:
--
--   1. a unitary $\hat U$ with $\hat U\hat A = \sqrt{\hat A^\dagger\hat A}$ exists (polar decomposition), also when $\hat A$ is not invertible;
--   2. every unitary maximizing $\mathrm{Re}[\mathrm{tr}(\hat U\hat A)]$ satisfies $\hat U\hat A = \sqrt{\hat A^\dagger\hat A}$.
--
--   This is the mathematical fact that turns the family of bounds (3.58) into the single tightest bound.
--
--   **Formalization Note** Each maximum is stated by `IsGreatest` on the set of values at unitaries, so attainment is included.
--
--   Differences from the source:
--   - reading: "The set of operators Û that gives rise to the maximum must satisfy ÛÂ = √(Â†Â)", with two maxima in (3.60) → stated for the maximizers of Re[tr(ÛÂ)]; reason: true for every Â under this reading; for the maximum of |tr(ÛÂ)| it is false as printed (a 1×1 matrix, Â = 1, Û = −1 gives |tr(ÛÂ)| = 1 and ÛÂ = −1), and a phase e^{iφ} is needed, as in (4.66), p.116
--   - encoding: max over unitaries → `IsGreatest` of the set of values; reason: the same statement, attainment included
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.60)–(3.61), p.53 (PDF p.62)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_FuchsVdGraaf_qBhattacharyya
open Matrix
open scoped MatrixOrder ComplexOrder
open WildeQIT FuchsVdGraaf

namespace FuchsThesis.Fidelity

/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.60)–(3.61), p.53 (PDF p.62): for any operator `Â`,
`max_Û |tr(ÛÂ)| = max_Û Re[tr(ÛÂ)] = tr √(Â†Â)`, the maximum over all unitary `Û`; a unitary with
`ÛÂ = √(Â†Â)` exists (polar decomposition); and a maximizer of `Re[tr(ÛÂ)]` satisfies
`ÛÂ = √(Â†Â)`.

**Formalization Note.** Each "max" is an `IsGreatest` over the set of values at unitaries, which
carries attainment. "The set of operators Û that gives rise to the maximum must satisfy (3.61)" is
read for the maximum of `Re[tr(ÛÂ)]`, the reading under which it is true for every `Â`. For the
maximum of `|tr(ÛÂ)|` it is false as printed: `e^{iφ}Û` maximizes too (`n` a singleton, `Â = 1`,
`Û = -1`); compare (4.66), p.116. `A` is any square matrix, invertible or not. -/
theorem eq_3_60 {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    IsGreatest {v : ℝ | ∃ U ∈ unitaryGroup n ℂ, v = ‖Matrix.trace (U * A)‖}
      (Matrix.trace (CFC.sqrt (Aᴴ * A))).re ∧
    IsGreatest {v : ℝ | ∃ U ∈ unitaryGroup n ℂ, v = (Matrix.trace (U * A)).re}
      (Matrix.trace (CFC.sqrt (Aᴴ * A))).re ∧
    (∃ U ∈ unitaryGroup n ℂ, U * A = CFC.sqrt (Aᴴ * A)) ∧
    ∀ U ∈ unitaryGroup n ℂ,
      (Matrix.trace (U * A)).re = (Matrix.trace (CFC.sqrt (Aᴴ * A))).re →
        U * A = CFC.sqrt (Aᴴ * A) := by sorry

end FuchsThesis.Fidelity
