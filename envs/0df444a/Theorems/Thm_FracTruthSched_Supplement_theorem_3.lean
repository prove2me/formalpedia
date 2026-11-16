-- Prove2me | Theorems.Thm_FracTruthSched_Supplement_theorem_3
-- name    : FracTruthSched.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:17:30.190799+00:00
-- url     : https://prove2.me/theorems/8fc56fab-fb24-4dc1-a90b-db5f093d865f
-- title:
--   Theorem 3 — the continuous case: jointly continuous disutilities force $\rho\ge(n+1)/2$
-- statement:
--   Fix $n\ge1$ machines and a real constant $\rho$. For $\ell\ge2$, $MC_\ell$ is the multi-clique with $\ell$ parallel tasks between every pair of machines and one self-loop at each machine; a graph input gives each machine nonnegative values on the core tasks it is incident to, and $C(t)$ is the optimal integral makespan of $t$ among eligible allocations.
--
--   Suppose that for every $\ell\ge2$ there is a feasible, truthful fractional mechanism $(x,P)$ on the core tasks of $MC_\ell$ such that
--
--   1. (i) edges are allocated only to their endpoints and self-loops only to their owners;
--   2. (ii) every edge with a unique zero-cost endpoint is allocated wholly to that endpoint;
--   3. (iii) the allocation satisfies zero-type irrelevance;
--   4. (iv) relabelling tasks within a class $Q_{\{i,j\}}$ relabels the allocation in the same way and leaves every disutility unchanged;
--   5. the bound (7) holds with the same $\rho$ for every $\ell$:
--   $$\mathrm{Mech}_x(t)\le\rho\,C(t)\qquad\text{for every graph input }t\text{ (including }C(t)=0);$$
--   6. every machine's disutility $V_i(t_i;t_{-i})$ is jointly continuous in all graph values.
--
--   Then
--   $$\rho\ \ge\ \frac{n+1}{2}.$$
--
--   This is the lower bound of Theorem 2 under the extra regularity assumption of continuous disutilities; continuity of allocations is not assumed.
--
--   Differences from the source:
--   - generalization: standing assumption n ≥ 2 of the lower-bound proof (§3.1, p.6) → every n ≥ 1 ([NeZero n]); reason: covers more; at n ≥ 2 it is the paper's statement, and n = 1 is included (the paper notes the bound is immediate there, proof of Theorem 2, p.18)
--   - encoding: truthful fractional mechanism on MC_ℓ, defined at all nonnegative real graph inputs → FracMech n (CoreTask n ℓ) with IsFeasibleOn IsGraphInput and IsTruthfulOn IsGraphInput (graph inputs as n × core-task matrices, zero at non-incident pairs); reason: the published base-mission encoding of Lemma 1; same mechanisms
--   - encoding: every machine's disutility function is jointly continuous on all graph values → ∀ i, ContinuousOn (fun t => disutility M t i) {t | IsGraphInput t} (product topology); reason: the graph-input set fixes every non-graph entry at 0, so continuity on it is continuity in all graph values of all machines jointly
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Theorem 3, p.10 (§3.3); properties (i)–(iv) and bound (7) of Lemma 1, p.9; Definition 1, p.5

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_disutility
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric

set_option autoImplicit false

namespace FracTruthSched.Supplement

open FracTruthSched

/-- **Theorem 3 (The continuous case)** (Anastasiadis et al., *Tight bounds for fractional and
randomized truthful scheduling*, arXiv:2611.06642v1, Theorem 3, p.10). Suppose that, for every
`ℓ ≥ 2`, there is a truthful fractional mechanism on `MC_ℓ` satisfying properties (i)–(iv) of
Lemma 1 and the bound (7) with the same constant `ρ`, and every machine's disutility function is
jointly continuous on all graph values. Then `ρ ≥ (n + 1)/2`.

**Formalization Note.** Machines are `Fin n` with `n ≥ 1` (`[NeZero n]`; the paper's standing
`n ≥ 2` of §3.1 is not assumed, and for `n = 1` the claim is `ρ ≥ 1`). `ρ` is one real constant,
fixed before `ℓ`; the mechanism may depend on `ℓ`. "Truthful fractional mechanism on `MC_ℓ`" is
feasibility and truthfulness (1) on graph inputs (`IsGraphInput`: nonnegative, zero off the
incident pairs), as in the published Lemma 1. (i)–(iv) are `IsEligible`, `HasUniqueZeros`,
`HasZeroTypeIrrelevance`, `IsClassSymmetric`; (7) is required at every graph input, including
`C(t) = 0`. Joint continuity: for every machine `i`, `t ↦ V_i(t_i; t_{-i})` (`disutility`) is
continuous on the set of graph inputs in the product topology, i.e. in all graph values of all
machines at once. Nothing is assumed about continuity of allocations or payments. -/
theorem theorem_3 {n : ℕ} [NeZero n] (ρ : ℝ)
    (h : ∀ ℓ : ℕ, 2 ≤ ℓ → ∃ M : FracMech n (CoreTask n ℓ),
      IsFeasibleOn IsGraphInput M ∧ IsTruthfulOn IsGraphInput M ∧
      IsEligible M ∧ HasUniqueZeros M ∧ HasZeroTypeIrrelevance M ∧ IsClassSymmetric M ∧
      (∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) ∧
      ∀ i : Fin n, ContinuousOn (fun t => disutility M t i) {t | IsGraphInput t}) :
    ((n : ℝ) + 1) / 2 ≤ ρ := by sorry

end FracTruthSched.Supplement
