-- Prove2me | Theorems.Thm_LDPSelect_lemma_16
-- name    : LDPSelect.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:14.178056+00:00
-- url     : https://prove2.me/theorems/15ea6a4d-5790-4ff7-b1c4-27630ab27bb7
-- title:
--   Lemma 16 — two-state separation: the gap $W^{\mathrm I}-W^{\mathrm N}$ is exactly $\Delta(a)$
-- statement:
--   Let $a>1$, $\mu>0$, $\delta=\frac{(a-1)\mu}{2(a+2)}$, $\ell=\mu-\delta$, $h=\mu+\delta$, and $Y$ uniform on $\{0,\mu,2\mu\}$. Let $\mathcal F$ be downward closed, let the first two arrivals be $u$ and $v$, and let all later arrivals have deterministic values $\tau$. Suppose
--
--   1. $v$ is feasible whether or not $u$ was accepted ($\{u,v\}\in\mathcal F$);
--   2. the thresholds $(t_0,t_1)$ faced by $v$ in the two states are $(\ell,h)$ or $(h,\ell)$;
--   3. the continuation values after rejecting and after accepting $u$ differ by $\gamma\ge\delta$.
--
--   With $X_v=Y$ and $X_u$ uniform on $\{0,2\gamma\}$, the interactive value is finite and
--
--   $$W^{\mathrm I}_{\mathcal F}-W^{\mathrm N}_{\mathcal F}=\Delta(a).$$
--
--   One lemma separates all nine four-element obstructions and every $B_m$.
--
--   Differences from the source:
--   - encoding: the gap W^I − W^N equals ∆(a) → W^I < ∞ and W^I = W^N + ∆(a) in [0, ∞]; reason: with W^I finite this is the real equation W^I − W^N = ∆(a)
--   - encoding: γ, the difference of the continuation values → γ = (β₀ + F_a(Y, t₀)) − (β₁ + F_a(Y, t₁)), rejection minus acceptance; reason: the sign convention of A.6, p.19
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
--   - encoding: an output space for each user → one output type per mechanism; reason: a family of output spaces embeds in its disjoint union, and privacy is preserved
--   - encoding: decisions using independent algorithmic randomness → a Markov acceptance kernel at each step (behaviour strategy); reason: with perfect recall a mixture over decision rules is a behaviour strategy, and public randomness is conditioned on (Definition 8)
--   - encoding: the selected set stays in F → the acceptance kernel puts no mass on accepting when A ∪ {i} ∉ F, at every history; reason: changing a rule on unreachable histories does not change its reward
--   - encoding: optimal expected rewards → suprema in [0, ∞] over all output types and mechanisms; reason: for integrable priors both values are finite, so no junk value arises
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 16, p.9 (pdf p.10); ∆(a) in Proposition 12, p.6 (pdf p.7)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_TwoState

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 16, p.9.

Suppose the first two arrivals are `u` and `v`, all later values are deterministic, `v` is feasible
whether or not `u` was accepted, in the two states the threshold faced by `v` takes the values `ℓ` and
`h`, and the continuation values differ by `γ ≥ δ`. With `X_v = Y` and `X_u` uniform on `{0, 2γ}`, the
gap `W^I − W^N` equals `∆(a)`.

**Formalization Note.** `u` is position `0` and `v` is position `1`. `γ` is signed, rejection minus
acceptance, as A.6 defines it. The gap is an equation in `ℝ≥0∞` with `W^I` finite, so it is a real
difference. -/
theorem lemma_16 {m : ℕ} (a μ : ℝ) (ha : 1 < a) (hμ : 0 < μ) (F : Family (m + 2))
    (hF : IsDownClosed F) (τ : Fin (m + 2) → ℝ≥0) (huv : ({0, 1} : Finset (Fin (m + 2))) ∈ F)
    (ht : (t0 F τ = ell a μ ∧ t1 F τ = high a μ) ∨ (t0 F τ = high a μ ∧ t1 F τ = ell a μ))
    (hγ : deltaParam a μ ≤ gammaOf a μ F τ) :
    WI a F (twoStatePrior (gammaOf a μ F τ) μ τ) ≠ ⊤ ∧
    WI a F (twoStatePrior (gammaOf a μ F τ) μ τ) =
      WN a F (twoStatePrior (gammaOf a μ F τ) μ τ) + ENNReal.ofReal (gapDelta a μ) := by sorry

end LDPSelect
