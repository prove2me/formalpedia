-- Prove2me | Theorems.Thm_LDPSelect_B_instance
-- name    : LDPSelect.B_instance
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:11.1842+00:00
-- url     : https://prove2.me/theorems/47e85308-65c9-43b6-915d-2fd9e41c0b5d
-- title:
--   §5 — the instance of $B_m$: the gap is $\Delta(a)$
-- statement:
--   Let $a>1$, $\mu>0$ and $m\ge4$. In $B_m$, let two elements of $[m]$ arrive first, the first uniform on $\{0,2\mu\}$ and the second $Y$ uniform on $\{0,\mu,2\mu\}$, then the remaining $m-2$ elements of $[m]$ with value $\ell$, and finally $x$ with value $(m-2)\ell+h$. The thresholds are $h$ and $\ell$, $\gamma=\mu$, $W^{\mathrm I}$ is finite and
--
--   $$W^{\mathrm I}_{B_m}-W^{\mathrm N}_{B_m}=\Delta(a).$$
--
--   This is the separation for the infinite family of excluded minors.
--
--   Differences from the source:
--   - encoding: the gap W^I − W^N equals ∆(a) → W^I < ∞ and W^I = W^N + ∆(a) in [0, ∞]; reason: with W^I finite this is the real equation W^I − W^N = ∆(a)
--   - encoding: two elements of [m] arrive first, x last → the natural order of Fin (m+1), with x = Fin.last m; reason: B_m is symmetric in the elements of [m]
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §5, p.9 (pdf p.10)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Obstructions
import Definitions.Def_LDPSelect_TableA6

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §5, p.9.

For `B_m`, let two elements of `[m]` arrive first, then the remaining `m − 2` elements of `[m]` with value
`ℓ`, and finally `x` with value `(m − 2) ℓ + h`; with the first arrival uniform on `{0, 2μ}` and the second
`Y`, the thresholds are `h` and `ℓ`, `γ = μ`, and the gap `W^I − W^N` is `∆(a)`.

**Formalization Note.** The arrival order is the order of `Fin (m + 1)`, with `x = Fin.last m` last, and
the first two arrivals are positions `0, 1`. -/
theorem B_instance (a μ : ℝ) (ha : 1 < a) (hμ : 0 < μ) (m : ℕ) (hm : 4 ≤ m) :
    WI a (B m) (bPrior a μ m) ≠ ⊤ ∧
    WI a (B m) (bPrior a μ m) =
      WN a (B m) (bPrior a μ m) + ENNReal.ofReal (gapDelta a μ) := by sorry

end LDPSelect
