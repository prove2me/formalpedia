-- Prove2me | Theorems.Thm_LDPSelect_table_A6
-- name    : LDPSelect.table_A6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:51.733309+00:00
-- url     : https://prove2.me/theorems/6e7713a4-1dcd-426e-84ff-731fe8b392f4
-- title:
--   A.6 — the instances of the nine four-element obstructions satisfy Lemma 16
-- statement:
--   Let $a>1$ and $\mu>0$. For each $i=1,\dots,9$, take $O_i$ in the arrival order of its row of the table in A.6, with the two deterministic tail values of the row. Then the thresholds $(t_0,t_1)$, the continuations $(\beta_0,\beta_1)$ and $\gamma$ are those listed, $\gamma\ge\delta$, and with the first arrival uniform on $\{0,2\gamma\}$ and the second $Y$, $W^{\mathrm I}$ is finite and
--
--   $$W^{\mathrm I}-W^{\mathrm N}=\Delta(a).$$
--
--   Every listed four-element obstruction therefore admits a bounded instance on which interaction strictly helps.
--
--   Differences from the source:
--   - encoding: the gap W^I − W^N equals ∆(a) → W^I < ∞ and W^I = W^N + ∆(a) in [0, ∞]; reason: with W^I finite this is the real equation W^I − W^N = ∆(a)
--   - encoding: the arrival order 1, 3, 2, 4 → the relabelling of O_i by the transposition of positions 1 and 2 of Fin 4; reason: position 1 holds the paper's element 3
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), A.6, p.19 (pdf p.20)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Obstructions
import Definitions.Def_LDPSelect_TableA6

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), A.6, p.19.

In each row of the table, with the listed arrival order and tail values, the thresholds of the second
arrival are `(t_0, t_1)`, the continuations after accepting it are `(β_0, β_1)`, the difference of
continuation values is `γ`, and the gap `W^I − W^N` is `∆(a)`.

**Formalization Note.** The table lists the data; Lemma 16 yields the gap, stated here for the row's
instance. -/
theorem table_A6 (a μ : ℝ) (ha : 1 < a) (hμ : 0 < μ) (i : Fin 9) :
    let r := a6Row a μ i
    let F : Family (2 + 2) := relabel (a6Order i) (O i)
    let τ := a6Tail r
    t0 F τ = r.t0 ∧ t1 F τ = r.t1 ∧ tailCont F τ {1} = r.β0 ∧ tailCont F τ {0, 1} = r.β1 ∧
      gammaOf a μ F τ = r.γ ∧ deltaParam a μ ≤ r.γ ∧
      WI a F (twoStatePrior r.γ μ τ) ≠ ⊤ ∧
      WI a F (twoStatePrior r.γ μ τ) =
        WN a F (twoStatePrior r.γ μ τ) + ENNReal.ofReal (gapDelta a μ) := by sorry

end LDPSelect
