-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_lemma_7_4_1
-- name    : MDPFinance.LPDuality.lemma_7_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:52:33.251997+00:00
-- url     : https://prove2.me/theorems/fa802092-9296-4446-98b2-75cb343cd825
-- title:
--   Lemma 7.4.1 — positive-model monotone bounds, existence of J
-- statement:
--   The mirror image of chunk `07a`'s Lemma 7.1.4 for positive models: the $n$-stage value functions
--   $J_n^\pi$, $J_n$ are bounded *below* (rather than above) by an $m$-stage value minus a
--   shrinking-tail correction $T_\circ^m\varepsilon$. This monotonicity is what guarantees the
--   finite-horizon values converge (from below) to genuine limits $J_\infty^\pi$, $J$ — the positive-
--   model analogue of the existence argument chunk `07a` gave for the general (upper-bounded) theory.
--
--   **Moderation note.** Under the section's standing Integrability Assumption (A), $\varepsilon<\infty$ (`hAneg`), without which the extended-real stage values can be $\infty-\infty$; Lemma 7.4.1(a) is for $\pi\in F^\infty$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 209, Lemma 7.4.1

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

/-- Lemma 7.4.1 (Bäuerle–Rieder, p. 209, PDF 220), the positive-model (`(C^-)`) mirror image of
`MDPFinance.Contracting.lemma_7_1_4` (chunk `07a`). For `n, m \in \mathbb N_0` with `n \ge m` it
holds that a) `J_n^\pi \ge J_m^\pi - T_\circ^m\varepsilon`. b) `J_n \ge J_m - T_\circ^m
\varepsilon`. This monotonicity implies `J_\infty^\pi = \lim_n J_n^\pi$ and `J(x) := \lim_n
J_n(x)` exist; note `J_\infty^\pi \ge -\varepsilon`. For `π ∈ F^∞`, under the section's
standing Integrability Assumption (A), `ε < ∞`. -/
theorem lemma_7_4_1 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hAneg : IntegrabilityAssumptionAneg M)
    (π : ℕ → E → A) (hπ : IsPolicyOf M π) (n m : ℕ) (hnm : m ≤ n) (x : E) :
    (Jnpi M M.r π m x - (Tcirc M)^[m] (epsilon M) x ≤ Jnpi M M.r π n x ∧
        Jn M M.r m x - (Tcirc M)^[m] (epsilon M) x ≤ Jn M M.r n x) ∧
      (∀ x', -epsilon M x' ≤ Jinfpi M M.r π x') := by sorry

end MDPFinance.LPDuality
