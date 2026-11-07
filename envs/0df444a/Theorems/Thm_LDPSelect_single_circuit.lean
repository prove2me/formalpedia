-- Prove2me | Theorems.Thm_LDPSelect_single_circuit
-- name    : LDPSelect.single_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:21.768337+00:00
-- url     : https://prove2.me/theorems/98ad4214-319d-40f9-831b-a29b8c7d3fe9
-- title:
--   Proof of Lemma 13 — a single circuit: one threshold per user, so $W^{\mathrm N}=W^{\mathrm I}$
-- statement:
--   Let $a\ge1$ and let $C$ be a nonempty set of users. Let $\mathcal F=\{S : S\subsetneq C\}$, the single circuit $U_{|C|-1,|C|}$ on $C$, every user outside $C$ being a loop. For every integrable product prior,
--
--   $$W^{\mathrm N}_{\mathcal F}=W^{\mathrm I}_{\mathcal F}.$$
--
--   This is the step of the proof of Lemma 13 on $U_{m-1,m}$: before the first rejection there is a single undecided state and after it every remaining element is accepted, so each user meets one threshold determined by deterministic continuation values, and fixing the optimal kernel of Lemma 9 for that threshold attains the interactive Bellman value. It is one of the two kinds of component of the class $\mathcal G$.
--
--   Differences from the source:
--   - generalization: 1 < a (fixed in §3.1, p.6, and Theorem 2, p.2) → 1 ≤ a; reason: the case a = 1 is added; at a > 1 the statement is the source's
--   - generalization: U_{m−1,m} on its own ground set → U_{m−1,m} inside Fin n, every other element a loop; reason: taking the whole ground set gives the source's case; loops are never accepted, and they let a component's arrivals interleave with others (Lemma 20)
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), proof of Lemma 13, p.7 (pdf p.8)

import Mathlib
import Definitions.Def_LDPSelect_Values

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), proof of Lemma 13, p.7.

For a single circuit `C`, with every element outside `C` a loop, each user meets one threshold, and a
fixed kernel attains the interactive Bellman value: `W^N = W^I`.

**Formalization Note.** The feasible sets are the proper subsets of `C`. Elements outside `C` are loops,
which is how a component meets arrivals interleaved with other components. `C` is nonempty so that the
family is nonempty. -/
theorem single_circuit {n : ℕ} (a : ℝ) (ha : 1 ≤ a) (C : Finset (Fin n)) (hC : C.Nonempty)
    (P : Fin n → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)] (hP : IsIntegrablePrior P) :
    WN a {S | S ⊂ C} P = WI a {S | S ⊂ C} P := by sorry

end LDPSelect
