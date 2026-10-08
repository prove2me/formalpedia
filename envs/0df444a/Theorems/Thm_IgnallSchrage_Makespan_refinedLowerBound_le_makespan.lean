-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_refinedLowerBound_le_makespan
-- name    : IgnallSchrage.Makespan.refinedLowerBound_le_makespan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:48:33.909198+00:00
-- url     : https://prove2.me/theorems/e6cff872-664d-46e9-b075-8a8fd9dd9ead
-- title:
--   p. 409 — the refined bound used in the 3-machine computations is a lower bound
-- statement:
--   Let $J_r$ be a node with $r<n$ jobs and $\sigma$ any full sequence that begins with $J_r$. Then the refined bound of p. 409, in which $\mathrm{TIMEB}(J_r)$ is replaced by $\max[\mathrm{TIMEB}(J_r),\mathrm{TIMEA}(J_r)+\min_{\bar J_r}a_i]$ and $\mathrm{TIMEC}(J_r)$ by $\max[\mathrm{TIMEC}(J_r),\mathrm{TIMEB}(J_r)+\min_{\bar J_r}b_i,\mathrm{TIMEA}(J_r)+\min_{\bar J_r}(a_i+b_i)]$, satisfies
--
--   $$
--   LB'(J_r)\ \le\ \mathrm{makespan}(\sigma).
--   $$
--
--   The paper only reports that this bound "was used" in its computations; its use in branch and bound is valid exactly because it is still a lower bound, which is what this statement asserts.
--
--   **Formalization Note** The paper does not state the inequality explicitly; it is the property the use of the bound in the procedure requires. No sign condition on processing times is assumed.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 409, refined lower bound

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_RefinedLowerBound

namespace IgnallSchrage.Makespan

/-- p. 409: the refined bound used in the 3-machine computations is still a lower bound: for a
node `J = J_r` with `r < n` and every full sequence `σ` beginning with `J_r`, the refined bound
is at most the makespan of `σ`. -/
theorem refinedLowerBound_le_makespan {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n))
    (hJ : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    refinedLowerBound a b c J ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan
