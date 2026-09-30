-- Prove2me | Theorems.Thm_InventoryControl_roundy_serial
-- name    : InventoryControl.roundy_serial
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:13:21.32183+00:00
-- url     : https://prove2.me/theorems/184afe8c-95c7-4292-8ad8-ff7b4091e065
-- title:
--   Roundy's 98 % approximation for a serial system: a nested powers-of-two policy within $1/(\sqrt2\ln 2)$ of the relaxed optimum
-- statement:
--   Roundy's 98 % approximation for a serial system, the capstone of Chapter 9.
--
--   A serial inventory system has $N$ installations; installation $i$ produces item $i$ from one
--   unit of item $i+1$, and item 1 faces a constant continuous demand $d > 0$. There are
--   ordering costs $A_i > 0$ and echelon holding costs $e_i > 0$ at all stages, no shortages,
--   zero lead-times, and constant batch quantities $Q_i > 0$, with cost per time unit
--
--   $$ C(Q) \;=\; \sum_{i=1}^{N}\Big(e_i\frac{Q_i}{2} + A_i\frac{d}{Q_i}\Big). $$
--
--   Let $Q^{\mathrm{rel}}$ minimize $C$ subject to the relaxed nesting constraints
--   $Q_{i-1} \le Q_i$ (Eq. 9.18). Then there are a basic quantity $q > 0$ and integers
--   $m_1 \le m_2 \le \dots \le m_N$ such that the batch quantities $Q_i = 2^{m_i}q$ satisfy
--   Roundy's constraints (9.16), $Q_i = 2^{k_i}Q_{i-1}$ with $k_i \ge 0$, and
--
--   $$ C\big(2^{m}q\big) \;\le\; \frac{1}{\sqrt 2\,\ln 2}\,C\big(Q^{\mathrm{rel}}\big)
--      \;\approx\; 1.0201\,C\big(Q^{\mathrm{rel}}\big). $$
--
--   Since every policy satisfying (9.16) satisfies (9.18), $C(Q^{\mathrm{rel}})$ is a lower bound
--   on the cost of any nested constant-batch policy, so Roundy's solution is within 2 % of the
--   best such policy. The book adds that the same bound holds against the optimum over all
--   policies, including those whose batch quantities vary over time, by the Lagrangean argument
--   around Eq. (9.21); that stronger comparison class is not modelled here.
--
--   The proof combines the powers-of-two analysis of Sect. 7.1 with the structure of the relaxed
--   optimum. The multipliers of the Lagrangean relaxation (9.19)-(9.20) turn the relaxed problem
--   into $N$ independent EOQ problems with modified holding costs $e_i'$ whose solution is
--   $Q^{\mathrm{rel}}$; Proposition 7.2 applied to those independent problems gives a $q$ whose
--   rounding costs at most $1/(\sqrt 2\ln 2)$ times $C'(Q^{\mathrm{rel}})$ under the modified costs,
--   and complementary slackness (the multipliers vanish unless the constraint is tight, and equal
--   quantities round to equal quantities) transfers the bound to the original costs. The
--   rounding is monotone, so the result is nested.
--
--   **Formalization Note** The comparison class is stated explicitly: $Q^{\mathrm{rel}}$ is any
--   minimizer over positive batch quantities satisfying (9.18), and the conclusion exhibits $q$
--   and $m$. The constant is the exact $1/(\sqrt 2\ln 2)$ of Proposition 7.2, not a rounded
--   $1.02$.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 178-180, Sect. 9.2.2 'Roundy's 98% Approximation', Eq. (9.16)-(9.18), (9.22) and the paragraph after (9.22): 'We have feasible constant batch quantities and the cost increase compared to the optimal solution is at most 2 %, since it is at most 2 % compared to the lower bound (9.21)'; Roundy (1985, 1986)

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem roundy_serial {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (hd : 0 < d)
    (hA : ∀ i, 0 < A i) (he : ∀ i, 0 < e i) (Qrel : Fin N → ℝ) (hpos : ∀ i, 0 < Qrel i)
    (hnest : SerialNested Qrel)
    (hopt : ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
      serialCost A e d Qrel ≤ serialCost A e d Q) :
    ∃ q : ℝ, 0 < q ∧ ∃ m : Fin N → ℤ,
      SerialPowerOfTwo (fun i => (2 : ℝ) ^ (m i) * q)
        ∧ serialCost A e d (fun i => (2 : ℝ) ^ (m i) * q)
            ≤ 1 / (Real.sqrt 2 * Real.log 2) * serialCost A e d Qrel := by sorry

end InventoryControl
