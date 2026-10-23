-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_claim_p
-- name    : MonopolyDemandUncertainty.SBSMP.claim_p
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:26.921976+00:00
-- url     : https://prove2.me/theorems/e45250cc-8cf0-4796-82d3-3abf084124bb
-- title:
--   Claim P, p. 16 (PDF 17) — with only V1 = [v*1, v*12) and V12 nonempty, the scheme (v*1, v*12) maximizes profit from V12
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Conditions 1, 2 and 3. Let $\underline v \le v_1^* < v_{12}^* \le \bar v$, and let $(x,t)$ be a deterministic BIC and EIR mechanism in which only $V_1 = [v_1^*, v_{12}^*)$ and $V_{12} = [v_{12}^*, \bar v]$ are nonempty, i.e. for $v \in V$, $x_1(v) = 1$ iff $v \ge v_1^*$ and $x_2(v) = 1$ iff $v \ge v_{12}^*$, and suppose $t_1(v_1^*) = v_1^*$. Then, with $f_i = -D_i'$,
--   $$\int_{v_{12}^*}^{\bar v} \sum_i t_i(v)\,\alpha_i f_i(v)\,dv \;\le\; \int_{v_{12}^*}^{\bar v} \big(v_1^*\,\alpha_1 f_1(v) + v_{12}^*\,\alpha_2 f_2(v)\big)\,dv,$$
--   and the payment scheme $t_1 \equiv v_1^*$, $t_2 \equiv v_{12}^*$ on $V_{12}$, i.e. the state-by-state posted prices $(v_1^*, v_{12}^*)$, is BIC and EIR.
--
--   Claim P reduces the optimal mechanism with only $V_1$ and $V_{12}$ nonempty to posted prices, which is the last step before the optimization over the two prices.
--
--   **Formalization Note** "Maximizes profits from $V_{12}$ subject to all EIR and BIC constraints" is posed as: the profit from $V_{12}$ of every BIC and EIR mechanism of the stated shape is at most that of the scheme, and the scheme itself (which is the posted-price mechanism with prices $v_1^*$, $v_{12}^*$) is BIC and EIR.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 16, §A.5.6, Claim P (proof p. 17)

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Claim P, p. 16 (PDF 17), proof p. 17 (PDF 18): let `M` be BIC and EIR with only
`V₁ = [a, b)` and `V₁₂ = [b, v̄]` nonempty (`a = v₁*`, `b = v₁₂*`) and `t₁(v₁*) = v₁*`. Then the
profit from `V₁₂` is at most that of the scheme `t₁ ≡ a`, `t₂ ≡ b` on `V₁₂`, and that scheme
(the posted prices `a`, `b`) is BIC and EIR. -/
theorem claim_p (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) (a b : ℝ) (ha : E.vlo ≤ a) (hab : a < b) (hb : b ≤ E.vhi)
    (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M)
    (hx0 : ∀ v ∈ E.V, M.x 0 v = decide (a ≤ v)) (hx1 : ∀ v ∈ E.V, M.x 1 v = decide (b ≤ v))
    (hta : M.t 0 a = a) :
    (∫ v in Icc b E.vhi, ∑ i, M.t i v * E.prob i * E.dens i v ≤
        ∫ v in Icc b E.vhi, (a * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v)) ∧
      E.IsBIC (sbsmp a b) ∧ E.IsEIR (sbsmp a b) := by sorry
end MonopolyDemandUncertainty.SBSMP
