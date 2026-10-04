-- Prove2me | Theorems.Thm_MDPFinance_Contracting_lemma_7_1_4
-- name    : MDPFinance.Contracting.lemma_7_1_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:18.499442+00:00
-- url     : https://prove2.me/theorems/26ed6ed2-c973-4b29-bf56-bbd4aaa37778
-- title:
--   Lemma 7.1.4 — tail-truncation bound on the finite-horizon value functions
-- statement:
--   This lemma bounds how much the $n$-stage value $J_n^\pi$ (resp. $J_n$) can exceed the $m$-stage
--   value $J_m^\pi$ (resp. $J_m$) for $n \ge m$: the excess is controlled entirely by $T_\circ^m
--   \delta$, the $m$-fold-shifted bound on the *tail* of the discounted reward sum. It is the first
--   step toward showing $(J_n^\pi)$ and $(J_n)$ converge under the Convergence Assumption (C), since
--   $T_\circ^m\delta \to 0$ as $m \to \infty$ forces the excess to vanish.
--
--   **Moderation note.** Part a) is for policies $\pi\in F^\infty$ (`hπ`); for an infeasible sequence of maps the inequality can fail since $r$ is unconstrained off $D$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 197, Lemma 7.1.4

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- Lemma 7.1.4 (Bäuerle–Rieder, p. 197, PDF 208). For `n, m \in \mathbb N_0` with `n \ge m` it
holds: a) `J_n^\pi \le J_m^\pi + T^m_\circ \delta` for `π ∈ F^∞`. b) `J_n \le J_m + T^m_\circ \delta`. -/
theorem lemma_7_1_4 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (π : ℕ → E → A) (hπ : IsPolicyOf M π) (n m : ℕ) (hnm : m ≤ n) (x : E) :
    Jnpi M M.r π n x ≤ Jnpi M M.r π m x + (Tcirc M)^[m] (delta M) x ∧
      Jn M M.r n x ≤ Jn M M.r m x + (Tcirc M)^[m] (delta M) x := by sorry

end MDPFinance.Contracting
