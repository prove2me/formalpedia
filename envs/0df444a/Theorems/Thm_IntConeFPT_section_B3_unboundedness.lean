-- Prove2me | Theorems.Thm_IntConeFPT_section_B3_unboundedness
-- name    : IntConeFPT.section_B3_unboundedness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:15.13666+00:00
-- url     : https://prove2.me/theorems/274103d7-d21c-4b04-baf8-4ce2ab10d376
-- title:
--   Section B.3 — a feasible instance is unbounded below iff some homogeneous representation has negative cost
-- statement:
--   Let $I$ be a valid instance of (♣) that has a feasible representation. Then (♣) is unbounded below if and only if there are multiplicities $\lambda$ (generators in the $S^{(t)}$, nonnegative integer values) with
--   $$
--   \sum_t(y^{(t)},v^{(t)})\in\hat Q,\qquad((y^{(t)},v^{(t)},N^{(t)}))_{t=1}^{\tau}\in\hat{\mathcal A},\qquad\mathrm{cost}(\lambda)<0,
--   $$
--   where $\hat Q$ and $\hat{\mathcal A}$ are the descriptions of $Q$ and $\mathcal A$ with right-hand sides replaced by zero.
--
--   The proof of Theorem 1 (p.18) uses this to turn a non-negative optimum of the homogeneous instance into boundedness of the original one.
--
--   **Formalization Note** $\hat Q$ and $\hat{\mathcal A}$ are `Instance.Qhat` and `Instance.Ahat`.
--
--   Differences from the source:
--   - reading: "the homogeneous aggregate constraints" → Σ_t (y^(t), v^(t)) ∈ Q̂ and ((y^(t), v^(t), N^(t)))_t ∈ Â, the instance's systems with zero right-hand side; reason: this is how the proof of Theorem 1 (p.18) forms them; for a feasible instance they describe the recession cone of the aggregate constraints
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Section B.3, p.40 (used in the proof of Theorem 1, p.18)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Section B.3: unboundedness criterion.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Section B.3, p.40: "To justify the unboundedness test, assume
that a feasible representation has already been found. … If its objective is unbounded below, its
LP relaxation has a rational improving recession direction. Scaling the direction makes all counts
integral; its continuous blocks then define a negative-cost representation satisfying the
homogeneous aggregate constraints. Conversely, adding any such representation repeatedly to a
feasible representation proves unboundedness." (Used in the proof of Theorem 1, p.18.)

A feasible valid instance is unbounded below if and only if some representation (generators in
the `S^(t)`, nonnegative integer multiplicities) satisfies the homogeneous aggregate constraints
`Σ_t (y^(t), v^(t)) ∈ Q̂`, `((y^(t), v^(t), N^(t)))_t ∈ Â` (the descriptions of `Q`, `A` with zero
right-hand side, p.18) and has negative cost.

**Formalization Note.** `Q̂` and `Â` are `Instance.Qhat` and `Instance.Ahat`. -/
theorem section_B3_unboundedness (I : Instance) (hI : I.Valid) (hfeas : ∃ μ, I.Feasible μ) :
    I.Unbounded ↔
      ∃ μ : Mult I, I.Supported μ ∧ I.totalAgg μ ∈ I.Qhat ∧
        (fun t => I.typeAgg μ t) ∈ I.Ahat ∧ I.cost μ < 0 := by sorry

end IntConeFPT
