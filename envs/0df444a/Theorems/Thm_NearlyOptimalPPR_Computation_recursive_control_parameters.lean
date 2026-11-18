-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
-- name    : NearlyOptimalPPR.Computation.recursive_control_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:31:06.481225+00:00
-- url     : https://prove2.me/theorems/c7e91c40-a513-45cb-af63-d0573815bd83
-- title:
--   Depth, budgets, cache control, and positive parameters
-- statement:
--   Consider any finite execution prefix of Algorithms 6–9 at prescribed depth $\ell$. The stack top never exceeds $\ell$. For every open frame its budget flag equals the control predicate that is true exactly in the full-solve, normalize, leaf-drain, after-child, and finish-episode states. A cache can be nonempty only at the final level; leaf-drain occurs only there, and the full-solve state has empty cache.
--
--   If the initial threshold is positive, every open frame has threshold $q_j>0$, block parameter $b_j\ge1$, and an open budget implies $\theta_j\ge q_j$:
--
--   $$q>0\ \Longrightarrow\ \forall j\le\mathrm{top},\quad q_j>0,\quad b_j\ge1,\quad \mathrm{openBudget}_j\Longrightarrow\theta_j\ge q_j.$$
--
--   These control invariants apply to actual finite prefixes without assuming termination or successful return. They justify the guards and threshold comparisons used in recursive numerical preservation.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, equation (1) p.6, equation (4) p.17 and Algorithms 6–9 pp.20–22; finite-prefix invariants used in Lemmas 3.7 and 4.3.

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section

theorem NearlyOptimalPPR.Computation.recursive_control_parameters (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    st.top ≤ ℓ ∧ BudgetInvariant st ∧ CacheControlInvariant ℓ st ∧ (0 < q → ParameterInvariant st) := by sorry
