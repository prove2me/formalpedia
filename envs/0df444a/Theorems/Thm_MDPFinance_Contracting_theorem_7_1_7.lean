-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_1_7
-- name    : MDPFinance.Contracting.theorem_7_1_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:36.985866+00:00
-- url     : https://prove2.me/theorems/acab796b-90ea-4c34-8d16-87cdd5e498b5
-- title:
--   Theorem 7.1.7 (Verification Theorem) — fixed points of T above J∞ are optimal
-- statement:
--   This is the infinite-horizon verification theorem, structurally identical in role to chunk
--   `02a`'s finite-horizon Theorem 2.3.7: it turns the hard existence problem (does an optimal policy
--   exist, and what is it?) into an easy verification problem (check a *candidate* satisfies two
--   conditions). If $v$ is a fixed point of $T$ in the regularity class $IB$ with $v \ge J_\infty$,
--   and $f^*$ is a maximizer of $v$, then $v$ *is* the true value function $J_\infty$, and the
--   stationary policy $(f^*,f^*,\dots)$ is optimal. No structural hypothesis on the whole model is
--   needed beyond the Convergence Assumption (C) — the theorem works from a single exhibited fixed
--   point.
--
--   **Moderation note.** The chapter's standing Integrability Assumption (A), $\delta<\infty$, is a hypothesis (`hA`); it is not implied by the Convergence Assumption (C) as formalized (the tail $T_\circ^n\delta\to 0$ says nothing about $\delta$ itself), and the values are only the book's expectations under it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 199, Theorem 7.1.7

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Theorem 7.1.7 (Verification Theorem) (Bäuerle–Rieder, p. 199, PDF 210 (corrected from BRIEF.md's "p. 198"; the printed footer at PDF 210 reads 199)). Assume (C) and let
`v \in IB` be a fixed point of `T` such that `v \ge J_\infty`. If `f^*` is a maximizer of `v`,
then `v = J_\infty` and the stationary policy `(f^*,f^*,\dots)` is optimal for the infinite-stage
Markov Decision Model. The chapter's standing Integrability Assumption (A) is `hA`. -/
theorem theorem_7_1_7 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hA : IntegrabilityAssumptionA M)
    (hC : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (delta M) x) atTop (𝓝 (0 : EReal)))
    (v : E → EReal) (hvIB : v ∈ IB M) (hvfix : v = T M v) (hvge : ∀ x, Jinf M x ≤ v x)
    (fstar : E → A) (hfstar : IsMaximizerOf M v fstar) :
    v = Jinf M ∧ ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x := by sorry

end MDPFinance.Contracting
