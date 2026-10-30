-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_claim_4
-- name    : MonopolyDemandUncertainty.SBSMP.claim_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:31.854984+00:00
-- url     : https://prove2.me/theorems/75e6096d-9de7-40c5-a9c1-09f71ce6c46d
-- title:
--   Claim 4, p. 13 (PDF 14), under Condition 4(ii) (the case of Lemma A.3) — the scheme (t1(v*1), v*12) maximizes profit from V12
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Conditions 1, 2, 3 and 4(ii). Let $v_2^* < v_1^* < v_{12}^*$ with $\underline v \le v_2^*$ and $v_{12}^* \le \bar v$, let $V_{12} = [v_{12}^*, \bar v]$, and set, as in (A.30),
--   $$T_1 = v_1^* - (v_1^* - v_2^*)\frac{\alpha_2}{\alpha_1 Z(v_1^*)}.$$
--   For a payment scheme $s = (s_1, s_2)$ on $V_{12}$ (types of $V_{12}$ consume in both states) consider the constraints
--
--   1. the BIC constraint of $v_{12}^*$ with respect to $v_1^*$, who consumes in state 1 only and pays $T_1$: $\sum_i (v_{12}^* - s_i(v_{12}^*))\alpha_i f_i(v_{12}^*) \ge (v_{12}^* - T_1)\alpha_1 f_1(v_{12}^*)$;
--   2. the BIC constraint of every $v \in (v_{12}^*, \bar v]$ with respect to $v_{12}^*$;
--   3. the EIR constraint of $v_{12}^*$: $0 \le s_i(v_{12}^*) \le v_{12}^*$;
--   4. $s_2(v_{12}^*) \ge v_2^*$;
--   5. $s_1(v_{12}^*) \ge T_1$,
--
--   where $f_i = -D_i'$. Then the constant scheme $s_1 \equiv T_1$, $s_2 \equiv v_{12}^*$ satisfies 1–5, and every scheme satisfying 1–5 has
--   $$\int_{v_{12}^*}^{\bar v} \sum_i s_i(v)\,\alpha_i f_i(v)\,dv \;\le\; \int_{v_{12}^*}^{\bar v} \big(T_1\,\alpha_1 f_1(v) + v_{12}^*\,\alpha_2 f_2(v)\big)\,dv.$$
--
--   Claim 4 computes the best payments from the types who buy in both states, given the prices of the lower sets, and is a step of the appendix's bound on mechanisms with $V_1$, $V_2$ and $V_{12}$ all nonempty.
--
--   **Formalization Note** Condition 4(ii) is added: Claim 4 is used inside Lemma A.3, which assumes it, and without it $T_1$ can be negative, so the scheme would violate EIR. Constraint 3 includes $0 \le s_i(v_{12}^*)$, which is EIR (2); (A.34) prints only the upper bounds. The integral is a Lebesgue set integral over $[v_{12}^*,\bar v]$ ($0$ for a non-integrable integrand).
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 13, §A.4.9, Claim 4, with (A.30) p. 12 and (A.32)–(A.34) p. 13

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Claim 4, p. 13 (PDF 14), under Condition 4(ii) (the case of Lemma A.3, where it is used).
With `a₂ = v₂* < a₁ = v₁* < b = v₁₂*` and `V₁₂ = [b, v̄]`, the constant scheme
`(t₁, t₂) ≡ (t₁(v₁*), b)` on `V₁₂`, with `t₁(v₁*)` from (A.30), satisfies the constraints (i)–(v)
and its profit from `V₁₂` is at least that of every scheme satisfying (i)–(v). -/
theorem claim_4 (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) (h4 : E.Condition4ii) (a₁ a₂ b : ℝ) (hlo : E.vlo ≤ a₂)
    (h21 : a₂ < a₁) (h1b : a₁ < b) (hb : b ≤ E.vhi) :
    E.Claim4Feasible a₁ a₂ b ![fun _ => E.claim4T1 a₁ a₂, fun _ => b] ∧
      ∀ s : Fin 2 → ℝ → ℝ, E.Claim4Feasible a₁ a₂ b s →
        ∫ v in Icc b E.vhi, ∑ i, s i v * E.prob i * E.dens i v ≤
          ∫ v in Icc b E.vhi,
            (E.claim4T1 a₁ a₂ * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v) := by sorry
end MonopolyDemandUncertainty.SBSMP
