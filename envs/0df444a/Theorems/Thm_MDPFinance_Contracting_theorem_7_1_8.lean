-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_1_8
-- name    : MDPFinance.Contracting.theorem_7_1_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:53.620114+00:00
-- url     : https://prove2.me/theorems/fe45ec1c-cfe6-478e-b448-0c3c8698382a
-- title:
--   Theorem 7.1.8 (Structure Theorem) — value iteration and optimality under (SA)
-- statement:
--   Under the Convergence Assumption (C) and the Structure Assumption (SA) — a closed class $IM$
--   containing $0$, mapped into itself by $T$, on which maximizers always exist, and additionally
--   containing the limit value function $J$ as one of its own fixed points — the infinite-horizon
--   value function $J_\infty$ coincides with $J = \lim_n J_n$: value iteration genuinely computes the
--   true value. Moreover $J_\infty$ is the *largest* function in $IM$ that is $r$-subharmonic
--   ($v \le Tv$) and dominated by $\delta$, and an optimal stationary policy exists, built from any
--   maximizer of $J_\infty$. This is the general infinite-horizon analogue of chunk `02a`'s finite-
--   horizon Structure Theorem, and the direct predecessor of this mission's goal (Theorem 7.3.5),
--   which sharpens it under a contraction hypothesis.
--
--   **Moderation note.** The chapter's standing Integrability Assumption (A), $\delta<\infty$, is a hypothesis (`hA`); it is not implied by the Convergence Assumption (C) as formalized (the tail $T_\circ^n\delta\to 0$ says nothing about $\delta$ itself), and the values are only the book's expectations under it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 200, Theorem 7.1.8

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Theorem 7.1.8 (Structure Theorem) (Bäuerle–Rieder, p. 200, PDF 211 (corrected from BRIEF.md's "p. 199")). Let (C) and the
Structure Assumption (SA) be satisfied. Then it holds: a) `J_\infty \in IM`, `J_\infty = TJ_\infty`
and `J_\infty = J = \lim_n J_n` (Value Iteration). b) `J_\infty` is the largest `r`-subharmonic
function `v` in `IM \cap IB`, i.e. `J_\infty` is the largest function `v \in IM` with `v \le Tv`
and `v \le \delta`. c) There exists a maximizer `f \in \Delta` of `J_\infty`, and every maximizer
`f^*` of `J_\infty` defines an optimal stationary policy `(f^*,f^*,\dots)`. The chapter's standing
Integrability Assumption (A) is `hA`. -/
theorem theorem_7_1_8 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hA : IntegrabilityAssumptionA M)
    (hC : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (delta M) x) atTop (𝓝 (0 : EReal)))
    (IM' : Set (E → EReal)) (Δ : Set (E → A)) (hSA : StructureAssumptionSA M IM' Δ (Jlim M)) :
    (Jinf M ∈ IM' ∧ Jinf M = T M (Jinf M) ∧ Jinf M = Jlim M) ∧
      (Jinf M ∈ IM' ∧ (∀ x, Jinf M x ≤ T M (Jinf M) x) ∧ (∀ x, Jinf M x ≤ delta M x) ∧
        ∀ v ∈ IM', (∀ x, v x ≤ T M v x) → (∀ x, v x ≤ delta M x) → ∀ x, v x ≤ Jinf M x) ∧
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
