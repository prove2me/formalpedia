-- Prove2me | Theorems.Thm_FracTruthSched_lemma_4
-- name    : FracTruthSched.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:00.430947+00:00
-- url     : https://prove2.me/theorems/047642b2-e82e-481d-b331-bb257d6e25aa
-- title:
--   Lemma 4 — the root's disutility is nondecreasing in the opposing values
-- statement:
--   Let $\ell\ge2$ and let $(x,P)$ be a feasible truthful mechanism on the graph inputs of $MC_\ell$ satisfying eligibility (i) and zero-type irrelevance (iii). Fix a root $i$ and vary only its values $t$ on its incident edges and the opposing endpoint values $s$ on those edges; fix all other values. Then the root's disutility function $V(t;s)$ is nondecreasing in each coordinate of $s$.
--
--   Formally: if graph inputs $t,t'$ agree everywhere except at the other endpoints' values on edges incident to $i$, and $t\le t'$ entrywise, then $V_i(t)\le V_i(t')$.
--
--   This monotonicity replaces continuity in the general case: it yields measurable versions of the disutilities and the choice of a common leaf value in Lemma 5.
--
--   Differences from the source:
--   - generalization: a limit mechanism on MC_ℓ (Definition 6: the mechanism constructed in Lemma 1) → every feasible truthful mechanism on the graph inputs of MC_ℓ with eligibility (i) and zero-type irrelevance (iii); reason: the proof uses exactly truthfulness (area formula (5), WMON of the opposing machine), eligibility, feasibility and zero-type irrelevance; every limit mechanism has these properties by Lemma 1, so the statement specializes to the source's
--   - encoding: V(t; s) nondecreasing in each coordinate of s → t ≤ t′ entrywise with t, t′ agreeing outside the opposing endpoints' values on the root's incident edges implies V_i(t) ≤ V_i(t′); reason: monotone in each coordinate is equivalent to monotone in the coordinatewise order
--   - encoding: a graph input of MC_ℓ: the two endpoint values of every edge and the owner value of every self-loop, all nonnegative, and no other values → t : Fin n → CoreTask n ℓ → ℝ, nonnegative and 0 at every (machine, task) pair that is not incident (IsGraphInput); edges of Q{u,v} are encoded with u < v; reason: a machine's cost Σ_e t_ie x_ie is then its cost on its incident tasks; same inputs and same costs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 4, p.17

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_disutility

set_option autoImplicit false

namespace FracTruthSched

/-- **Lemma 4 (monotonicity in opposing values)** (Anastasiadis et al., arXiv:2611.06642v1, Lemma 4,
p.17). Fix a root `i` and vary only its values on its incident edges and the opposing endpoint values
`s` on those edges; fix all other values. Then the root's disutility `V(t; s)` is nondecreasing in each
coordinate of `s`.

**Formalization Note.** Stated for every feasible truthful mechanism on `MC_ℓ` (graph inputs) with
eligibility (i) and zero-type irrelevance (iii), the properties the proof uses; every limit mechanism
of Lemma 1 has them. Two graph inputs `t, t'` agreeing everywhere except at the opposing endpoints'
values on edges incident to `i`, with `t ≤ t'` pointwise, give `V_i(t) ≤ V_i(t')`: this is
nondecreasingness in each coordinate of `s` (the root's own values may be any fixed values). -/
theorem lemma_4 {n ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M) (i : Fin n)
    (t t' : Fin n → CoreTask n ℓ → ℝ) (ht : IsGraphInput t) (ht' : IsGraphInput t')
    (hfix : ∀ u e, (u = i ∨ ¬ (e.isLeft ∧ incident i e)) → t u e = t' u e)
    (hle : ∀ u e, t u e ≤ t' u e) :
    disutility M t i ≤ disutility M t' i := by sorry

end FracTruthSched
