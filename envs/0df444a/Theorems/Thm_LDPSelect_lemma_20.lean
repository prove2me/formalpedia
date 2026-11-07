-- Prove2me | Theorems.Thm_LDPSelect_lemma_20
-- name    : LDPSelect.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:05.102133+00:00
-- url     : https://prove2.me/theorems/b6879f8f-c210-4ee6-962d-2456411614b9
-- title:
--   Lemma 20 — additivity of $W^{\mathrm I}$, $W^{\mathrm N}$ and $M_{\mathcal F}$ over direct sums
-- statement:
--   Let $a\ge1$ and let $\mathcal F$ be downward closed. Let $c$ label the users by a finite set of indices $j$ such that $\mathcal F$ is the direct sum of its parts: $S\in\mathcal F$ if and only if $S\cap c^{-1}(j)\in\mathcal F$ for every $j$. Write $\mathcal F_j=\{S\in\mathcal F : S\subseteq c^{-1}(j)\}$. Then for every integrable product prior, in every interleaving of the parts given by $c$,
--
--   $$W^{\mathrm I}_{\mathcal F}=\sum_j W^{\mathrm I}_{\mathcal F_j},\qquad W^{\mathrm N}_{\mathcal F}=\sum_j W^{\mathrm N}_{\mathcal F_j},\qquad M_{\mathcal F}=\sum_j M_{\mathcal F_j}.$$
--
--   This reduces both directions of the classification to one component at a time.
--
--   Differences from the source:
--   - encoding: F_j on its own ground set → F_j on the whole ground set, users with another label being loops; reason: loops are never accepted, so the values agree, and no law has to be re-indexed
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 20, A.2, p.16 (pdf p.17)

import Mathlib
import Definitions.Def_LDPSelect_Values

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 20, p.16.

If `F = ⊕_j F_j` on disjoint ground sets, then for every interleaved arrival order
`W^I_F = ∑_j W^I_{F_j}`, `W^N_F = ∑_j W^N_{F_j}` and `M_F = ∑_j M_{F_j}`.

**Formalization Note.** A labelling `c` of the elements gives the disjoint ground sets, in any
interleaving. `F_j` is taken on the same `Fin n`, so elements with another label are loops, and no laws
need re-indexing. The direct sum is the condition `S ∈ F ↔ ∀ j, S ∩ c⁻¹(j) ∈ F`. -/
theorem lemma_20 {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (ha : 1 ≤ a)
    (F : Family n) (hF : IsDownClosed F) (c : Fin n → ι)
    (hc : ∀ S : Finset (Fin n), S ∈ F ↔ ∀ j, S.filter (fun e => c e = j) ∈ F)
    (P : Fin n → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)] (hP : IsIntegrablePrior P) :
    WI a F P = ∑ j, WI a {S | S ∈ F ∧ ∀ e ∈ S, c e = j} P ∧
    WN a F P = ∑ j, WN a {S | S ∈ F ∧ ∀ e ∈ S, c e = j} P ∧
    prophet F P = ∑ j, prophet {S | S ∈ F ∧ ∀ e ∈ S, c e = j} P := by sorry

end LDPSelect
