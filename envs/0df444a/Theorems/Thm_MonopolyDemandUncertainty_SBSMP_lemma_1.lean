-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_lemma_1
-- name    : MonopolyDemandUncertainty.SBSMP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:20.172917+00:00
-- url     : https://prove2.me/theorems/76756f36-77a4-434f-a1a7-d39286fc29e3
-- title:
--   Lemma 1, p. 4 (PDF 5) — every BIC and EIR mechanism with V12 empty is strictly beaten by a BIC and EIR mechanism
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Condition 1. Let $(x,t)$ be a deterministic BIC and EIR mechanism in which no valuation consumes in both states, that is, $V_{12} = \emptyset$. Then there is a deterministic BIC and EIR mechanism $(x',t')$ with strictly higher profit:
--   $$\pi(x,t) < \pi(x',t').$$
--
--   This is the paper's Lemma 1, "at the monopoly firm's optimal EIR and BIC mechanism, $V_{12}$ is nonempty", posed so that it does not presuppose that an optimal mechanism exists. It removes the mechanisms that never sell in both states from the search for an optimum.
--
--   **Formalization Note** The page states the conclusion for "the optimal mechanism"; here it is the equivalent statement that every mechanism with $V_{12}=\emptyset$ is strictly improvable. The profit is a Lebesgue integral and is $0$ when the integrand is not integrable.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 4, Lemma 1 (proof p. 6, §A.1)

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Lemma 1, p. 4 (PDF 5), proof p. 6 (PDF 7): every BIC and EIR mechanism with `V₁₂ = ∅` (no
type consumes in both states) is strictly beaten in profit by some BIC and EIR mechanism.
This is the paper's "at the optimal EIR and BIC mechanism, `V₁₂` is nonempty", posed without
assuming that an optimum exists. -/
theorem lemma_1 (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hBIC : E.IsBIC M) (hEIR : E.IsEIR M)
    (hV12 : ∀ v ∈ E.V, ¬ (M.x 0 v = true ∧ M.x 1 v = true)) :
    ∃ M' : Mechanism, E.IsBIC M' ∧ E.IsEIR M' ∧ E.profit M < E.profit M' := by sorry
end MonopolyDemandUncertainty.SBSMP
