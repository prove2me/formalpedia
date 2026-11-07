-- Prove2me | Theorems.Thm_LDPSelect_bellman_recursion
-- name    : LDPSelect.bellman_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:58.862232+00:00
-- url     : https://prove2.me/theorems/65114e9c-c2e2-4ef2-a744-56ba547dca4e
-- title:
--   §6 and A.8 — the interactive optimum is the Bellman value over position and accepted set
-- statement:
--   Let $a\ge1$, let $\mathcal F$ be downward closed, and let the values $X_1,\dots,X_n$ be independent and integrable. Then
--
--   $$W^{\mathrm I}_{\mathcal F}=V_1(\emptyset),$$
--
--   where $V$ is the Bellman recursion over (position, accepted set) with one-stage value (1): an optimal interactive policy depends only on the current position and the accepted set. Moreover $V_i$ is non-increasing in the accepted set: if $A\subseteq B$ are sets of earlier positions, then $V_i(B)\le V_i(A)$, so every threshold $V_{i+1}(A)-V_{i+1}(A\cup\{i\})$ is nonnegative, as (1) requires.
--
--   This identifies the "interactive Bellman value" that Lemma 13, Theorem 3 and A.5 compare against.
--
--   Differences from the source:
--   - reading: an optimal interactive policy depends only on the current position and the accepted set → W^I equals the value of the Bellman recursion over (position, accepted set) with one-stage value (1); reason: this is how the paper uses "the interactive Bellman value" and "the interactive Bellman recursion" (p.7)
--   - generalization: the Bellman recursion → the recursion, plus monotonicity of V_i in the accepted set; reason: an added conclusion; the source uses it when it writes v_{i+1} ≥ b_i (p.8) and when it feeds V_{i+1}(A) − V_{i+1}(A∪{i}) to (1), which needs s ≥ 0
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §6, p.10 (pdf p.11); A.8, p.21 (pdf p.22); "interactive Bellman value", p.7 (pdf p.8)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_bellman

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §6, p.10 and A.8, p.21, with display (1), p.5.

The interactive optimum depends only on the position and the accepted set: `W^I_F` is the Bellman value
at the start, and the Bellman value is non-increasing in the accepted set, so the threshold in each step
is nonnegative.

**Formalization Note.** Monotonicity is stated for accepted sets among earlier positions, the sets a
run can reach. -/
theorem bellman_recursion {n : ℕ} (a : ℝ) (ha : 1 ≤ a) (F : Family n) (hF : IsDownClosed F)
    (P : Fin n → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)] (hP : IsIntegrablePrior P) :
    WI a F P = ENNReal.ofReal (bellman a P F 0 ∅) ∧
    ∀ (i : ℕ) (A B : Finset (Fin n)), A ⊆ B → (∀ j ∈ B, j.val < i) →
      bellman a P F i B ≤ bellman a P F i A := by sorry

end LDPSelect
