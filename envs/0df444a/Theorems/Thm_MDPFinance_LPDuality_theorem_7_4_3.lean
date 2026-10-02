-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_4_3
-- name    : MDPFinance.LPDuality.theorem_7_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:52:37.97437+00:00
-- url     : https://prove2.me/theorems/7916ee36-0b84-4606-92b1-288d294f686e
-- title:
--   Theorem 7.4.3 — value iteration and smallest-superharmonic-majorant for positive models
-- statement:
--   For positive Markov Decision Models, value iteration again converges to the true value
--   ($J_\infty = TJ_\infty = J$), but the characterization reverses relative to chunk `07a`'s general
--   theory: $J_\infty$ is now the *smallest* $r$-superharmonic function dominating $-\varepsilon$
--   (rather than the largest subharmonic one bounded by $\delta$) — the structural mirror image
--   forced by controlling the reward's negative, rather than positive, part.
--
--   **Moderation note.** Under the section's standing Integrability Assumption (A) (`hAneg`); the competitors $v$ in b) are measurable $[-\infty,\infty]$-valued functions ($J_\infty=+\infty$ is possible in a positive model, so $\mathbb M(E)$ is not the right class).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 209, Theorem 7.4.3

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.LPDuality

/-- Theorem 7.4.3 (Bäuerle–Rieder, p. 209, PDF 220). Let `(C^-)` be satisfied. Then it holds:
a) `J_\infty = TJ_\infty` and `J_\infty = J` (Value Iteration). b) `J_\infty` is the smallest
`r`-superharmonic function `v` with `v \ge -\varepsilon`, i.e. `J_\infty` is the smallest function
`v` with `v \ge Tv` and `v \ge -\varepsilon` (among measurable `v : E → [-∞,∞]`; `J_∞ = +∞` is
possible in a positive model). The section's standing Integrability Assumption (A) is `hAneg`. -/
theorem theorem_7_4_3 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hAneg : IntegrabilityAssumptionAneg M)
    (hCneg : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (epsilon M) x) atTop (𝓝 (0 : EReal))) :
    (Jinf M = T M (Jinf M) ∧ Jinf M = Jlim M) ∧
      ((∀ x, T M (Jinf M) x ≤ Jinf M x) ∧ (∀ x, -epsilon M x ≤ Jinf M x) ∧
        ∀ v : E → EReal, Measurable v → (∀ x, T M v x ≤ v x) → (∀ x, -epsilon M x ≤ v x) →
          ∀ x, Jinf M x ≤ v x) := by sorry

end MDPFinance.LPDuality
