-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_prop_3_sequential_thresholds
-- name    : InfoSharing.Diseconomy.prop_3_sequential_thresholds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:26:15.888063+00:00
-- url     : https://prove2.me/theorems/0d68904b-485f-41a0-b6cd-0cdb533f8717
-- title:
--   Proposition 3 — the sequential thresholds $c_d^{S1}$ and $c_d^{S2}$
-- statement:
--   For every $\phi > 0$ there are thresholds $c_d^{S1}$, $c_d^{S2}$, depending only on $\phi$, with the following property. For every signal model, every $a$, $b > 0$, $c_d > 0$, every pricing-equilibrium family and either first manufacturer $k$, the set $N^S$ of numbers of informed manufacturers on the paths of subgame-perfect equilibria of sequential contracting satisfies
--
--   $$N^S = \{0\} \text{ if } 0 < c_d < c_d^{S1},\qquad 1 \in N^S \text{ if } c_d^{S1} \le c_d < c_d^{S2},\qquad 2 \in N^S \text{ if } c_d^{S2} \le c_d,$$
--
--   and $N^S = \{1\}$ for $c_d^{S1} < c_d < c_d^{S2}$, $N^S = \{2\}$ for $c_d > c_d^{S2}$.
--
--   Unlike concurrent contracting, partial sharing occurs for intermediate diseconomy.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$. At the two thresholds the retailer is indifferent, which is why the closed ends of the regions state only that the value is attained.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, Proposition 3

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

universe u

/-- Proposition 3, p. 253: there exist `c_d^{S1}` and `c_d^{S2}`, depending only on `φ`, such
that under sequential information contracting (either manufacturer `k` first)
`n_d^S = 0` if `0 < c_d < c_d^{S1}`, `n_d^S = 1` if `c_d^{S1} ≤ c_d < c_d^{S2}`, and `n_d^S = 2`
if `c_d^{S2} ≤ c_d`. On each closed region the value is attained by an SPE; on its interior
every SPE has that value. -/
theorem prop_3_sequential_thresholds :
    ∀ φ : ℝ, 0 < φ → ∃ cS1 cS2 : ℝ,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ) (a b c σ β : ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      IsSignalModel μ θ Y σ β → 0 < b → 0 < c → IsPricingEqFamily μ θ Y a b c φ β E → ∀ k : Fin 2,
      let P := payoffTable μ θ Y a b c φ E
      (c < cS1 → SeqOptN P k = {0}) ∧
      (cS1 ≤ c → c < cS2 → 1 ∈ SeqOptN P k) ∧
      (cS1 < c → c < cS2 → SeqOptN P k = {1}) ∧
      (cS2 ≤ c → 2 ∈ SeqOptN P k) ∧
      (cS2 < c → SeqOptN P k = {2}) := by sorry

end InfoSharing.Diseconomy
