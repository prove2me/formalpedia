-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_tildeG_subset
-- name    : LocalRademacher.StarHull.tildeG_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:28:25.240601+00:00
-- url     : https://prove2.me/theorems/497ac17c-9bf2-4fbe-b273-138b8936d730
-- title:
--   Proof of Theorem 3.3 (second part), p. 17 — G̃ᵣ ⊂ {f ∈ star(F, 0) : T(f) ≤ r}
-- statement:
--   Let $\mathcal F$ be a class of real functions on $\mathcal X$, let $r > 0$, and let $T$ be a functional on real functions such that, for every $f \in \mathcal F$,
--   1. $T(f) \ge 0$, and
--   2. $T(\alpha f) \le \alpha^2 T(f)$ for every $\alpha \in [0,1]$.
--
--   Then the rescaled class $\tilde{\mathcal G}_r = \{ r f / (T(f) \vee r) : f \in \mathcal F \}$ is contained in the local class of the star-hull:
--   $$
--   \tilde{\mathcal G}_r \subset \{ f \in \operatorname{star}(\mathcal F, 0) : T(f) \le r \}.
--   $$
--
--   The containment transfers the hypothesis of Theorem 3.3 (part 2), a bound on the Rademacher average of the local class, to the class $\tilde{\mathcal G}_r$ on which the concentration inequality is applied.
--
--   **Formalization Note** The two conditions on $T$ are imposed only on $\mathcal F$, as in the paper (no condition on $T$ elsewhere on the star-hull).
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Proof of Theorem 3.3, second part, p. 17, second sentence

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace LocalRademacher.StarHull

/-- **Containment of the rescaled class** (Proof of Theorem 3.3, second part, p. 17). Let
`r > 0`, and let `T` be a functional that is nonnegative on `F` and satisfies `T(αf) ≤ α² T(f)`
for `f ∈ F` and `α ∈ [0, 1]`. Then `G̃ᵣ = {r f / (T(f) ∨ r) : f ∈ F}` is contained in
`{f ∈ star(F, 0) : T(f) ≤ r}`. -/
theorem tildeG_subset {X : Type*} (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (r : ℝ) (hr : 0 < r)
    (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f) :
    tildeG F T r ⊆ localClass F T r := by sorry

end LocalRademacher.StarHull
