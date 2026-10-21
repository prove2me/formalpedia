-- Prove2me | Theorems.Thm_IntMul_Kappa_R6_rG_normalize
-- name    : IntMul.Kappa.R6.rG_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T23:13:46.167161+00:00
-- url     : https://prove2.me/theorems/a8b367da-5f63-4502-8ca7-905d27ab25cf
-- title:
--   Normalizing a crude-guard assembly to a round-six parameter record
-- statement:
--   Let $a_b, a_c \ge 0$ be bit and complex savings with $1 - a_b > 0$ and $1 - a_c > 0$, and suppose the crude-guard assembly `CrudeAssembly` holds for $(a_b, a_c, \beta = 1/1000, \varepsilon, x, C_1, \kappa)$ with complex width $m_c$ and rank sum $s_c$. Then there is an admissible round-six parameter record $P$ with
--   $$\kappa < P.\mathrm{gap}, \qquad P.\tau = 1 - a_b, \qquad P.\sigma = 1 - a_c, \qquad 2 + m_c \log s_c \le P.C_1.$$
--   This is xuanji's `r6_normalize` with Jain's round-six histograms replaced by the positivity of the two exponents, so it applies to any networks.
-- source:
--   xuanji's round-six development on Prove2me (Def_IntMul_Kappa_R6_Defs1, Defs16), Jain round seven data (Def_IntMul_KappaJainData).

import Definitions.Def_IntMul_Kappa_R6_Defs1
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R6

theorem rG_normalize (mc sc : ℕ) (ab ac ε x C₁ κ : ℝ)
    (hτ : 0 < 1 - ab) (hσ : 0 < 1 - ac) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ mc sc) :
    ∃ P : Prm, P.Ok ∧ κ < P.gap ∧ P.τ = 1 - ab ∧ P.σ = 1 - ac ∧
      2 + mc * Real.log sc ≤ P.C1 := by
  sorry

end IntMul.Kappa.R6
