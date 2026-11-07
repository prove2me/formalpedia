-- Prove2me | Theorems.Thm_LDPSelect_complete_multipartite
-- name    : LDPSelect.complete_multipartite
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:09.535725+00:00
-- url     : https://prove2.me/theorems/b777d024-bd9b-48b7-ad24-c01acbd7f7dc
-- title:
--   Proof of Theorem 3, sufficiency — a complete multipartite conflict graph: $W^{\mathrm N}=W^{\mathrm I}$
-- statement:
--   Let $a\ge1$, let $c$ be a set of users and $G$ a graph whose induced subgraph on $c$ is complete multipartite. Let $\mathcal F$ be the family of subsets of $c$ that are independent in $G$; users outside $c$ are loops. For every integrable product prior,
--
--   $$W^{\mathrm N}_{\mathcal F}=W^{\mathrm I}_{\mathcal F}.$$
--
--   This is the sufficiency paragraph of the proof of Theorem 3: the feasible sets are the subsets of one part, and before the first acceptance there is a single undecided state, so user $i$ meets the single threshold $v_{i+1}-b_i$ and a kernel fixed in advance attains the interactive Bellman value. It is the second kind of component of $\mathcal G$.
--
--   Differences from the source:
--   - generalization: 1 < a (fixed in Theorem 3, p.2) → 1 ≤ a; reason: the case a = 1 is added; at a > 1 the statement is the source's
--   - generalization: a complete multipartite conflict graph on its own ground set → a complete multipartite conflict graph inside Fin n, every other element a loop; reason: taking the whole ground set gives the source's case; loops are never accepted, and they let a component's arrivals interleave with others (Lemma 20)
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), proof of Theorem 3, Sufficiency, p.8 (pdf p.9)

import Mathlib
import Definitions.Def_LDPSelect_Values

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), proof of Theorem 3, Sufficiency, p.8.

For a complete multipartite conflict graph on `c`, with every element outside `c` a loop, each user meets
one threshold, and a fixed kernel attains the interactive Bellman value: `W^N = W^I`.

**Formalization Note.** The feasible sets are the subsets of `c` independent in `G`. Elements outside `c`
are loops, which is how a component meets arrivals interleaved with other components. `G` may have
edges outside `c`; they meet no feasible set. -/
theorem complete_multipartite {n : ℕ} (a : ℝ) (ha : 1 ≤ a) (c : Set (Fin n))
    (G : SimpleGraph (Fin n)) (hG : (G.induce c).IsCompleteMultipartite)
    (P : Fin n → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)] (hP : IsIntegrablePrior P) :
    WN a {S | (↑S : Set (Fin n)) ⊆ c ∧ G.IsIndepSet ↑S} P =
      WI a {S | (↑S : Set (Fin n)) ⊆ c ∧ G.IsIndepSet ↑S} P := by sorry

end LDPSelect
