-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_coupling_form
-- name    : ModelRiskOT.WorstProb.coupling_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:02:16.163898+00:00
-- url     : https://prove2.me/theorems/91cd1224-7756-4807-a5bd-057e77b2d2e9
-- title:
--   §2.2, p. 5 — coupling form of the primal for $f = 1_A$: $\sup\{P(A) : d_c(\mu,P) \le \delta\} = \sup\{\pi(S \times A) : \pi \in \Phi_{\mu,\delta}\}$
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1), $\mu$ a probability measure on $S$, $\delta > 0$, and $A \subseteq S$ a nonempty closed set. Then
--   $$\sup\{P(A) : d_c(\mu,P) \le \delta\} = \sup\{\pi(S \times A) : \pi \in \Phi_{\mu,\delta}\}.$$
--
--   This is the rewriting of the primal problem on p. 5, $\sup\{\int f\,d\nu : d_c(\mu,\nu) \le \delta\} = \sup\{\int f(y)\,d\pi(x,y) : \pi \in \Phi_{\mu,\delta}\}$, in the instance $f = 1_A$ used throughout §2.4. It turns an optimization over models $P$ into one over transport plans with fixed first marginal, which is the linear problem the duality theory treats.
--
--   **Formalization Note** Only the instance $f = 1_A$ is stated, which is how §2.4 uses the display ("$I(\pi) = \int 1_A(y)\,d\pi(x,y) = \pi(S \times A)$", p. 9). Values are in $[0,\infty]$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 5, §2.2 (display defining I), instance f = 1_A as on p. 9

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- §2.2, p. 5 (the display before (3)), for `f = 1_A` with `A` closed: the worst-case probability
over the optimal-transport ball equals its coupling form,
`sup {P(A) : d_c(μ, P) ≤ δ} = sup {π(S × A) : π ∈ Φ_{μ,δ}}`
(the instance used in §2.4, p. 9, "I(π) = ∫1_A(y)dπ(x, y) = π(S × A)"). -/
theorem coupling_form {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty) :
    worstProb c μ δ A = worstProbCoupling c μ δ A := by sorry

end ModelRiskOT.WorstProb
