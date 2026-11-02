-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_A1_R_imp_Rstar
-- name    : IntertempDUI.Finite.lemma_A1_R_imp_Rstar
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T16:15:00.820966+00:00
-- url     : https://prove2.me/theorems/647c5e94-2489-4b56-961b-c81a3880f7d0
-- title:
--   Lemma A1 (direction (R) ⟹ (R*)) on a finite horizon
-- statement:
--   Let $\mathcal T=[0,T]$ with $T>0$, let $\mathcal X$ be a connected topological space, and let $\mathcal A\subseteq C([0,T],\mathcal X)$ contain all constant trajectories. Let $\{\succsim_I\}_{I\in\mathcal I}$ be an intertemporal preference structure in which every $\succsim_I$ is complete and transitive, is nontrivial, and depends only on the restrictions of trajectories to $I$.
--
--   If $\mathcal A$ and $\{\succsim_I\}$ satisfy the richness condition **(R)**, then they also satisfy **(R\*)**. That is, for any disjoint time spans $Q,R$ and any $\alpha,\beta\in\mathcal A$ there is $\varphi\in\mathcal A$ such that
--   $$\varphi|_Q=\alpha|_Q\qquad\text{and}\qquad \varphi_J\approx_J\beta_J\ \text{ for every component interval } J \text{ of } R.$$
--
--   This is the half of Lemma A.1 that the finite-horizon theorems use: it lets the structural condition (R) of Theorem 1 replace (R\*), which is the hypothesis of Theorem B.1.
--
--   **Formalization Note.** Only this direction is stated. The converse $(R^*)\Rightarrow(R)$ is false for the platform's formal (R\*), because (R\*) prescribes a single trajectory on $Q$ while (R) glues two different ones.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, Math. Oper. Res. 46(3) (2021) 1203-1229; SSRN 3232014; HAL hal-03637876 (https://hal.science/hal-03637876v1), Appendix A, Lemma A.1 (p. 16 of the HAL version; p. 20 of the SSRN version), the direction "(R) implies (R*)" proved by induction over the component intervals of R.

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Lemma A1, p. 20, the direction (R) ⟹ (R*) on the finite horizon [0,T]. -/
theorem lemma_A1_R_imp_Rstar {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : Richness A pref) :
    RichnessStar A pref := by sorry

end IntertempDUI.Finite
