-- Prove2me | Theorems.Thm_IntMul_Kappa_R6_IL3H_p14NeedG_all
-- name    : IntMul.Kappa.R6.IL3H.p14NeedG_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T17:03:48.964826+00:00
-- url     : https://prove2.me/theorems/2f863fbf-8dff-4a45-886d-f2b2f4671772
-- title:
--   Uniform Proposition 14 for any complex network with a bounded child-width histogram
-- statement:
--   Let $h_c$ be a child-width histogram (pairs $(w, n_w)$) of a complex network of width $m_c$ with $W_c \ge 1$ roles, where $16 \le m_c \le 10^6$. Suppose every width satisfies $1 \le w \le w_{\max} \le m_c$, and for some $p_0 \ge 1$ with $p_0 \le 2 + m_c \log(\mathrm{histRankSum}\, h_c)$,
--   $$2 \Big(\sum_w n_w\Big) (2 w_{\max} + 1)^e \le (2 m_c)^e \quad \text{for every } e \ge p_0.$$
--   Then for every admissible round-six parameter record $P$, the parametric uniform Proposition 14 `P14NeedG Wc mc hc P` holds.
--
--   This is xuanji's `p14Need6_all` with Jain's histogram facts (widths at most 552, the numeric bound at exponent 600, and $C_1 \ge 600$) replaced by hypotheses, so it applies to any complex network.
-- source:
--   xuanji, round-six development on Prove2me (IntMul.Kappa.R6.IL3H.p14Need6_all and IntMul.Kappa.R6.kappa_final6_at), generalized to arbitrary network constants.

import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R6.IL3H

theorem p14NeedG_all (Wc mc wmax p₀ : ℕ) (hc : List (ℕ × ℕ))
    (hm16 : 16 ≤ mc) (hm' : mc ≤ 1000000) (hW1 : 1 ≤ Wc) (hwm : wmax ≤ mc)
    (hb : ∀ p ∈ hc, 1 ≤ p.1 ∧ p.1 ≤ wmax)
    (hnum : ∀ e, p₀ ≤ e → 2 * ((hc.map Prod.snd).sum * (2 * wmax + 1) ^ e) ≤ (2 * mc) ^ e)
    (hp₀ : (p₀ : ℝ) ≤ 2 + mc * Real.log (histRankSum hc)) (hp1 : 1 ≤ p₀)
    (P : Prm) (hP : P.Ok) : P14NeedG Wc mc hc P := by
  sorry

end IntMul.Kappa.R6.IL3H
