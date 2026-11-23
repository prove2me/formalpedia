-- Prove2me | Theorems.Thm_FracTruthSched_symmetrizeGen_properties_type0
-- name    : FracTruthSched.symmetrizeGen_properties_type0
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:06.50694+00:00
-- url     : https://prove2.me/theorems/405e3487-2bd0-4322-a61f-f1c800761d28
-- title:
--   General task-type Claim 1: symmetrization is feasible, truthful and equivariant (Type 0)
-- statement:
--   Let $(x,P)$ be a feasible truthful fractional mechanism on a finite task set, and let $G$ be a subgroup of its task permutations. Then its $G$-symmetrization is again feasible and truthful, and for every $\gamma\in G$,
--   $$\bar x_{ie}(\gamma s)=\bar x_{i,\gamma(e)}(s),\qquad \bar P_i(\gamma s)=\bar P_i(s).$$
--   This is Claim 1 with the task indexing type generalized from $\{0,\ldots,m-1\}$ to an arbitrary finite type, as needed for the explicit padded task index.
--
--   **Formalization Note.** This is the `Type 0` version of `FracTruthSched.symmetrizeGen_properties`; all finite task types constructed in the mission live in `Type 0`. The universe-polymorphic version currently triggers a statement-checker universe mismatch even when its `solution` has the identical statement.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.1, Claim 1, p.24; generalized finite indexing. Type-0 workaround for the statement checker on the universe-polymorphic target c06f7f27-ffde-47d2-bf73-dcc017ea4c30.

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_PaddedConstruction

set_option autoImplicit false

/-- General finite-task-type form of Claim 1: averaging over a subgroup of task
permutations preserves feasibility and truthfulness and is equivariant under those permutations.
This Type-0 version covers all of the paper's concretely encoded finite task sets. -/
theorem FracTruthSched.symmetrizeGen_properties_type0 {n : ℕ} {τ : Type} [Fintype τ]
    (M : FracMech n τ) (hfeas : IsFeasibleOn Nonneg M) (htruth : IsTruthfulOn Nonneg M)
    (G : Subgroup (Equiv.Perm τ)) :
    IsFeasibleOn Nonneg (symmetrizeGen M G) ∧ IsTruthfulOn Nonneg (symmetrizeGen M G) ∧
      ∀ γ ∈ G, ∀ (s : Fin n → τ → ℝ) (i : Fin n) (e : τ),
        (symmetrizeGen M G).x (relabel γ s) i e = (symmetrizeGen M G).x s i (γ e) ∧
          (symmetrizeGen M G).P (relabel γ s) i = (symmetrizeGen M G).P s i := by sorry
