-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_prop_4a_threshold_order
-- name    : InfoSharing.Diseconomy.prop_4a_threshold_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T06:30:00.887959+00:00
-- url     : https://prove2.me/theorems/04e9cc8f-ad34-49d3-898f-48cdc607fa54
-- title:
--   Proposition 4(a) — $c_d^{S1} < c_d^C < c_d^{S2}$
-- statement:
--   For every $\phi > 0$ there are thresholds $c_d^C$, $c_d^{S1}$, $c_d^{S2}$, depending only on $\phi$, that satisfy the conclusions of Proposition 2 (for $c_d^C$) and of Proposition 3 (for $c_d^{S1}, c_d^{S2}$, either first mover), and
--
--   $$c_d^{S1} < c_d^C < c_d^{S2}.$$
--
--   The ordering divides $c_d > 0$ into the four regions A–D of Figure 1, which the comparison of the two protocols uses.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 254, Proposition 4(a)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Diseconomy_IsConcurrentOutcome
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

universe u

/-- Proposition 4(a), p. 254: the thresholds of Propositions 2 and 3 satisfy
`c_d^{S1} < c_d^C < c_d^{S2}`. Stated as one existential: thresholds depending only on `φ` that
satisfy the conclusions of Propositions 2 and 3 and are so ordered. -/
theorem prop_4a_threshold_order :
    ∀ φ : ℝ, 0 < φ → ∃ cC cS1 cS2 : ℝ, cS1 < cC ∧ cC < cS2 ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ) (a b c σ β : ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      IsSignalModel μ θ Y σ β → 0 < b → 0 < c → IsPricingEqFamily μ θ Y a b c φ β E → ∀ k : Fin 2,
      let P := payoffTable μ θ Y a b c φ E
      ((c < cC → ConcOptN P = {0}) ∧
        (cC ≤ c → 2 ∈ ConcOptN P) ∧
        (cC < c → ConcOptN P = {2})) ∧
      ((c < cS1 → SeqOptN P k = {0}) ∧
        (cS1 ≤ c → c < cS2 → 1 ∈ SeqOptN P k) ∧
        (cS1 < c → c < cS2 → SeqOptN P k = {1}) ∧
        (cS2 ≤ c → 2 ∈ SeqOptN P k) ∧
        (cS2 < c → SeqOptN P k = {2})) := by sorry

end InfoSharing.Diseconomy
