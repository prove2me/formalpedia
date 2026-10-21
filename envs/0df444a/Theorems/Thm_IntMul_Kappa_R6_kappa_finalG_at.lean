-- Prove2me | Theorems.Thm_IntMul_Kappa_R6_kappa_finalG_at
-- name    : IntMul.Kappa.R6.kappa_finalG_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T17:04:03.875613+00:00
-- url     : https://prove2.me/theorems/a5b45724-98a9-4fea-8d92-360ea195b55b
-- title:
--   Round-six machine assembly, parametric in the bit and complex networks
-- statement:
--   Let $P$ be an admissible round-six parameter record with rational $\varepsilon$, and let $\kappa < P.\mathrm{gap}$. Assume the stack interfaces `SetupNeed6`, `CrtNeed6`, `FineNeed6`, `LineNeed6`, `P18IL6` at $P$, and the parametric Proposition 14 `P14NeedG Wc mc hc P`. Assume a bit network of width $m_b \ge 2$ with $W_b$ roles exists in the sense of `BitNetMomStmtG Wb mb hb`, and a complex network of width $m_c$ with $W_c$ roles and histogram $h_c$ exists in the gate class. Finally assume the moment and guard conditions
--   $$\mathrm{histMoment}(h_b, m_b, P.\tau) < W_b, \qquad \mathrm{histMoment}(h_c, m_c, P.\sigma) < W_c, \qquad 2 + m_c \log(\mathrm{histRankSum}\, h_c) \le P.C_1.$$
--   Then $\mathrm{KappaBound}(\kappa)$ holds: one multitape Turing machine multiplies $n$-bit integers in time $O(n\,L(n)^{1-\kappa})$.
--
--   This is xuanji's `kappa_final6_at` with Jain's round-six networks replaced by arbitrary ones, so any pair of certified networks plugs into the same machine.
-- source:
--   xuanji, round-six development on Prove2me (IntMul.Kappa.R6.IL3H.p14Need6_all and IntMul.Kappa.R6.kappa_final6_at), generalized to arbitrary network constants.

import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R6

theorem kappa_finalG_at (Wb mb Wc mc : ℕ) (hb hc : List (ℕ × ℕ)) (hmb : 2 ≤ mb)
    (P : Prm) (hP : P.Ok) (hq : ∃ q : ℚ, P.ε = q) (κ : ℝ) (hκ : κ < P.gap)
    (hSet : SetupNeed6 P) (hCrt : CrtNeed6 P) (hFine : FineNeed6 P) (hLine : LineNeed6 P)
    (hP14 : P14NeedG Wc mc hc P) (hP18 : P18IL6 P)
    (hJb : histMoment hb mb P.τ < Wb)
    (hJc : histMoment hc mc P.σ < Wc)
    (hC1 : 2 + mc * Real.log (histRankSum hc) ≤ P.C1)
    (hBit : Bit.BitNetMomStmtG Wb mb hb)
    (hCx : ∃ T, ∃ J : Cx.Prop8IfaceH Wc T mc hc, ∃ A, IL3H.GClassH J A) :
    IntMul.KappaBound κ := by
  sorry

end IntMul.Kappa.R6
