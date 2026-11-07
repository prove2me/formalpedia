-- Prove2me | Theorems.Thm_LDPSelect_lemma_15
-- name    : LDPSelect.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:36.934652+00:00
-- url     : https://prove2.me/theorems/d27f3aba-9dae-413c-99a7-9b6f0c971f3c
-- title:
--   Lemma 15 — a separation on a minor lifts to the family
-- statement:
--   Let $a\ge1$ and let $\mathcal F$ be downward closed. If $\mathcal F$ has a minor $\mathcal F/I_0\setminus E'$, with $I_0$ feasible, and that minor admits an instance with bounded values and $W^{\mathrm N}<W^{\mathrm I}$ (for some arrival order of the minor and some bounded product prior), then so does $\mathcal F$: there are an arrival order and a bounded product prior with $W^{\mathrm N}_{\mathcal F}<W^{\mathrm I}_{\mathcal F}$.
--
--   Differences from the source:
--   - generalization: 1 < a (fixed in §3.1, p.6, for the section containing Lemma 15) → 1 ≤ a; reason: the case a = 1 is added; at a > 1 the statement is the source's
--   - encoding: minors by repeated contraction and deletion, up to isomorphism → one contraction of a feasible set followed by one deletion, with an injective relabelling; reason: the paper's own reduction (§3.4, p.8): (F∖D)/I = (F/I)∖D
--   - encoding: every arrival order → every permutation σ relabelling F, with the prior indexed by arrival position; reason: a prior on users in order σ is a prior on positions
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 15, p.8 (pdf p.9)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_IsMinorOf

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 15, p.8.

If a downward-closed family `F` has a minor `F / I₀ \\ E′` with `I₀` feasible, and that minor admits an
instance with bounded values and `W^N < W^I`, then so does `F`.

**Formalization Note.** "Admits an instance" includes an arrival order of the minor, and the conclusion
gives an arrival order of `F`, as `HasGap` says. -/
theorem lemma_15 {k n : ℕ} (a : ℝ) (ha : 1 ≤ a) (F : Family n) (hF : IsDownClosed F)
    (O : Family k) (hO : IsMinorOf O F) (hgap : HasGap a O) : HasGap a F := by sorry

end LDPSelect
