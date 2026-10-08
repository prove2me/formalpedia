-- Prove2me | Theorems.Thm_MultistageStab_Value_case_costs_random
-- name    : MultistageStab.Value.case_costs_random
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:25.471102+00:00
-- url     : https://prove2.me/theorems/d91f8482-a732-4216-aef9-0140a02c1bf0
-- title:
--   Proof of Theorem 2.1, p. 6, case "only random costs" (r = 1, r′ = ∞) — v(ξ̃) − v(ξ) ≤ L(‖ξ̃ − ξ‖_1 + Σ‖x̄_τ − E[x̄_τ|F̃_τ]‖_∞) + ε
-- statement:
--   Work in the setting of program (1) when only the costs are random ($h_t$ deterministic, $r = 1$, $r' = \infty$). Assume (A1), $X_1$ bounded, $\xi$ admissible, $v(\xi)$ finite, and the level-boundedness of (A2) with constants $\alpha > 0$, $\delta > 0$. Then there is a constant $L > 0$ such that for every $\varepsilon \in (0,\alpha]$, every admissible $\tilde\xi$ with $\|\tilde\xi - \xi\|_1 < \delta$ and $v(\tilde\xi)$ finite, and every $\bar x \in l_\varepsilon(F(\xi,\cdot))$,
--   $$v(\tilde\xi) - v(\xi) \le L\Big( \|\tilde\xi - \xi\|_1 + \sum_{\tau=2}^{T-1} \big\|\bar x_\tau - \mathbb E[\bar x_\tau \mid \tilde{\mathcal F}_\tau]\big\|_\infty \Big) + \varepsilon .$$
--
--   This is the second case estimate in the proof of Theorem 2.1; here the decisions are essentially bounded.
--
--   **Formalization Note** As in the other case estimates, the inequality is stated in $[0,\infty]$ with its left-hand side truncated at $0$, and $\|\cdot\|_\infty$ is the essential supremum norm (`eLpNorm … ⊤`).
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), pp. 5–7, proof of Theorem 2.1, case "only random costs, i.e., r = 1 and r′ = ∞"

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem case_costs_random (D : Data) (hpat : Pattern.costs.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D)
    (hv_bot : value P D .costs ξ ≠ ⊥) (hv_top : value P D .costs ξ ≠ ⊤)
    (α δ : ℝ) (R : NNReal) (hα : 0 < α) (hδ : 0 < δ)
    (hA2 : LevelBoundedWith P D .costs ξ α δ R)
    (hA3 : Admissible P D .costs ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ α →
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D .costs ξ' →
        inputDist P D .costs ξ ξ' < ENNReal.ofReal δ →
        value P D .costs ξ' ≠ ⊥ → value P D .costs ξ' ≠ ⊤ →
        ∀ xbar ∈ levelSet P D .costs ξ ((value P D .costs ξ).toReal + ε),
          ENNReal.ofReal ((value P D .costs ξ').toReal - (value P D .costs ξ).toReal - ε) ≤
            ENNReal.ofReal L * (inputDist P D .costs ξ ξ' +
              ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xbar τ - P[xbar τ | sigmaGen ξ' τ]) ⊤ P) := by sorry

end MultistageStab.Value
