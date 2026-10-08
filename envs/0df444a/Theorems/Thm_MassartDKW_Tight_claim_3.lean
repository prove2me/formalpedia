-- Prove2me | Theorems.Thm_MassartDKW_Tight_claim_3
-- name    : MassartDKW.Tight.claim_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:11:50.433635+00:00
-- url     : https://prove2.me/theorems/6fea04e2-03dc-4bb5-b767-0e2265e1a628
-- title:
--   Claim 3 (2.9), p. 1276 — (1 + 12n(s − 2ε/3))⁻¹ ≥ (12ns)⁻¹ + ε²vₙ(s)/24n for n⁻¹ ≤ ε ≤ 3s/2
-- statement:
--   Let $n\ge1$ and $v_n(s)=\bigl(s(s^2-1/(4n^2))\bigr)^{-1}$. For positive $\varepsilon$ and $s$ with $n^{-1}\le\varepsilon\le3s/2$,
--   $$\Bigl(1+12n\Bigl(s-\frac{2\varepsilon}3\Bigr)\Bigr)^{-1}\ge(12ns)^{-1}+\frac{\varepsilon^2v_n(s)}{24n}.$$
--
--   With $s=2\varepsilon/3+j/n$ the left side is $(12j+1)^{-1}$, so the claim bounds the Stirling correction $C_j=\exp(-1/(12j+1))$ of (2.7) in the proof of Proposition 1.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1276, Claim 3, (2.9)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem claim_3 (n : ℕ) (hn : 1 ≤ n) (ε s : ℝ) (hε : 0 < ε) (hs : 0 < s)
    (h1 : 1 / (n : ℝ) ≤ ε) (h2 : ε ≤ 3 * s / 2) :
    1 / (12 * (n : ℝ) * s) + ε ^ 2 * v n s / (24 * (n : ℝ)) ≤ (1 + 12 * (n : ℝ) * (s - 2 * ε / 3))⁻¹ := by sorry

end MassartDKW.Tight
