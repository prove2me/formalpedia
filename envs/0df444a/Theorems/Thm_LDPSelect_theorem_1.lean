-- Prove2me | Theorems.Thm_LDPSelect_theorem_1
-- name    : LDPSelect.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:16.784376+00:00
-- url     : https://prove2.me/theorems/08d36c2c-aa1f-48b2-96b6-9351f7f9d3f9
-- title:
--   Theorem 1 — complete classification: interaction is useless exactly when each component is a single circuit or complete multipartite
-- statement:
--   Fix $1<a<\infty$ and a finite downward-closed family $\mathcal F$.
--
--   1. Interaction is useless for $\mathcal F$ (that is, $W^{\mathrm I}_{\mathcal F}=W^{\mathrm N}_{\mathcal F}$ for every product prior and every arrival order) if and only if every component either has exactly one minimally infeasible set, or has only two-element minimally infeasible sets forming a complete multipartite conflict graph (a free element forms a component of the second kind).
--   2. Equivalently, $\mathcal F$ has none of the nine four-element families $O_1,\dots,O_9$ and none of the families
--   $$B_m=\{S : S\subsetneq[m]\}\cup\{\{x\}\}\quad\text{on } [m]\cup\{x\},\ x\notin[m],\ m\ge4,$$
--   as a minor.
--   3. No finite list of excluded minors suffices: for every finite list of families, the families with none of them as a minor are not exactly the class of clause 1.
--   4. Whenever the condition fails, there are a bounded prior and an arrival order with $W^{\mathrm I}_{\mathcal F}>W^{\mathrm N}_{\mathcal F}$.
--
--   Here $W^{\mathrm I}$ and $W^{\mathrm N}$ are the optimal expected rewards of sequentially interactive and non-interactive $a$-locally private mechanisms; in both, the acceptance rule may depend on all past reports.
--
--   Differences from the source:
--   - reading: no finite list of excluded minors suffices → for every finite list L of families (on any ground sets), it is false that for all n and all downward-closed F on Fin n, F ∈ G ⇔ no member of L is a minor of F; reason: the strongest reading: the list is arbitrary, not a sublist of the printed one
--   - encoding: every product prior → every product of probability measures on ℝ≥0 with finite means; reason: the standing assumption of §2: values are independent and integrable
--   - encoding: minors by repeated contraction and deletion, up to isomorphism → one contraction of a feasible set followed by one deletion, with an injective relabelling; reason: the paper's own reduction (§3.4, p.8): (F∖D)/I = (F/I)∖D
--   - encoding: every arrival order → every permutation σ relabelling F, with the prior indexed by arrival position; reason: a prior on users in order σ is a prior on positions
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 1, pp.1–2 (pdf pp.2–3)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_InClass
import Definitions.Def_LDPSelect_IsMinorOf
import Definitions.Def_LDPSelect_Obstructions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 1, pp.1–2.

Fix `1 < a < ∞` and a finite downward-closed family `F`. (1) Interaction is useless for `F` if and only
if every component either has exactly one minimally infeasible set, or has only two-element minimally
infeasible sets forming a complete multipartite conflict graph. (2) Equivalently, `F` has none of the nine
four-element families and none of the `B_m`, `m ≥ 4`, as a minor. (3) No finite list of excluded minors
suffices. (4) Whenever the condition fails, there is a bounded prior and an arrival order with
`W^I_F > W^N_F`.

**Formalization Note.** `a` is real, with `a = e^ε` in the abstract. Clauses (2) and (3) do not involve
`a`. In (3) the list is arbitrary, of families on any finite ground sets: this is the strong reading. -/
theorem theorem_1 :
    (∀ a : ℝ, 1 < a → ∀ (n : ℕ) (F : Family n), IsDownClosed F → (Useless a F ↔ InClass F)) ∧
    (∀ (n : ℕ) (F : Family n), IsDownClosed F →
      (InClass F ↔ (∀ i, ¬ IsMinorOf (O i) F) ∧ ∀ m, 4 ≤ m → ¬ IsMinorOf (B m) F)) ∧
    (∀ L : List (Σ k, Family k), ¬ ∀ (n : ℕ) (F : Family n), IsDownClosed F →
      (InClass F ↔ ∀ e ∈ L, ¬ IsMinorOf e.2 F)) ∧
    (∀ a : ℝ, 1 < a → ∀ (n : ℕ) (F : Family n), IsDownClosed F → ¬ InClass F → HasGap a F) := by sorry

end LDPSelect
