-- Prove2me | Theorems.Thm_FracTruthSched_symmetrizeGen_properties
-- name    : FracTruthSched.symmetrizeGen_properties
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:52:01.015932+00:00
-- url     : https://prove2.me/theorems/c06f7f27-ffde-47d2-bf73-dcc017ea4c30
-- title:
--   General task-type Claim 1: symmetrization is feasible, truthful and equivariant
-- statement:
--   Let $(x,P)$ be a feasible truthful fractional mechanism on an arbitrary finite task set, and let $G$ be a subgroup of its task permutations. Then its $G$-symmetrization is again feasible and truthful, and for every $\gamma\in G$,
--   $$\bar x_{ie}(\gamma s)=\bar x_{i,\gamma(e)}(s),\qquad \bar P_i(\gamma s)=\bar P_i(s).$$
--   This is Claim 1 with the task indexing type generalized from $\{0,\ldots,m-1\}$ to an arbitrary finite type, as needed for the explicit padded task index.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.1, Claim 1, p.24; generalized finite indexing.

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_PaddedConstruction

set_option autoImplicit false

/-- General finite-task-type form of Claim 1: averaging over a subgroup of task
permutations preserves feasibility and truthfulness and is equivariant under those permutations. -/
theorem FracTruthSched.symmetrizeGen_properties {n : ℕ} {τ : Type*} [Fintype τ]
    (M : FracMech n τ) (hfeas : IsFeasibleOn Nonneg M) (htruth : IsTruthfulOn Nonneg M)
    (G : Subgroup (Equiv.Perm τ)) :
    IsFeasibleOn Nonneg (symmetrizeGen M G) ∧ IsTruthfulOn Nonneg (symmetrizeGen M G) ∧
      ∀ γ ∈ G, ∀ (s : Fin n → τ → ℝ) (i : Fin n) (e : τ),
        (symmetrizeGen M G).x (relabel γ s) i e = (symmetrizeGen M G).x s i (γ e) ∧
          (symmetrizeGen M G).P (relabel γ s) i = (symmetrizeGen M G).P s i := by sorry
