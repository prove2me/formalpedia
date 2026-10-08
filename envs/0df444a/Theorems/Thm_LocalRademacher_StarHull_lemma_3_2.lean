-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_lemma_3_2
-- name    : LocalRademacher.StarHull.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:28:09.069979+00:00
-- url     : https://prove2.me/theorems/e92ac25b-9908-4ba3-a028-7da6ed5360d2
-- title:
--   Lemma 3.2, p. 10 — a nontrivial sub-root ψ is continuous on (0, ∞), has a unique positive fixed point r*, and r ≥ ψ(r) iff r ≥ r*
-- statement:
--   A function $\psi : [0,\infty) \to [0,\infty)$ is **sub-root** if it is nonnegative, nondecreasing, and $r \mapsto \psi(r)/\sqrt r$ is nonincreasing on $r > 0$. It is **nontrivial** if it is not identically $0$.
--
--   Let $\psi$ be a nontrivial sub-root function. Then:
--   1. $\psi$ is continuous on $(0, \infty)$;
--   2. the equation $\psi(r) = r$ has exactly one solution $r^* > 0$;
--   3. for every $r > 0$,
--   $$
--   r \ge \psi(r) \iff r \ge r^*.
--   $$
--
--   The lemma justifies calling $r^*$ *the* fixed point of $\psi$, the quantity in terms of which all error bounds of the paper are stated; part 3 is how a level $r$ above the fixed point is recognised.
--
--   **Formalization Note** The page states continuity on $[0, \infty)$. This is a slip: $\psi(r) = \mathbf 1\{r > 0\}$ is a nontrivial sub-root function that is discontinuous at $0$, and the proof (Appendix A.2, p. 36) treats only points $y > 0$. Continuity is therefore stated on $(0,\infty)$. $\psi$ is a function on $\mathbb R$ of which only the values on $[0, \infty)$ are constrained (the published definition `IsSubRoot`); "nontrivial" is "$\psi(r) \ne 0$ for some $r \ge 0$".
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Lemma 3.2, p. 10 (Definition 3.1, p. 9; proof in Appendix A.2, pp. 36–37)

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace LocalRademacher.StarHull

/-- **Lemma 3.2** (p. 10, corrected continuity domain). A nontrivial sub-root function
`ψ` (Definition 3.1: nonnegative and nondecreasing on `[0, ∞)`, `r ↦ ψ(r)/√r` nonincreasing on
`r > 0`; nontrivial: not identically `0` on `[0, ∞)`) is continuous on `(0, ∞)`, the equation
`ψ(r) = r` has a unique positive solution `r*`, and for every `r > 0`, `ψ(r) ≤ r` iff `r* ≤ r`.
The page says "continuous on `[0, ∞)`"; `ψ(r) = 1{r > 0}` is a nontrivial sub-root function that
is discontinuous at `0`, so continuity is stated on `(0, ∞)`, which is what the proof (p. 36)
establishes. -/
theorem lemma_3_2 (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (hnt : ∃ r, 0 ≤ r ∧ ψ r ≠ 0) :
    ContinuousOn ψ (Set.Ioi 0) ∧ (∃! rstar : ℝ, 0 < rstar ∧ ψ rstar = rstar) ∧
      ∀ rstar : ℝ, 0 < rstar → ψ rstar = rstar → ∀ r : ℝ, 0 < r → (ψ r ≤ r ↔ rstar ≤ r) := by sorry

end LocalRademacher.StarHull
