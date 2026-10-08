-- Prove2me | Theorems.Thm_MassartDKW_Tight_claim_2
-- name    : MassartDKW.Tight.claim_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:08:51.153978+00:00
-- url     : https://prove2.me/theorems/3501b9c6-7eb0-4918-9e75-d979f3445c52
-- title:
--   Claim 2 (2.8), p. 1276 — (1 + 2ε/3s′)^{−1/2} ≤ (1 − ε/3s′ + ε²/6s′²) exp(−ε²vₙ(s′)/24n), corrected
-- statement:
--   Let $n\ge1$ and $v_n(s)=\bigl(s(s^2-1/(4n^2))\bigr)^{-1}$. For positive $\varepsilon$ and $s'$ with $n\varepsilon\ge2$, $ns'\ge1$ and $\varepsilon\le3s'$,
--   $$\Bigl(1+\frac{2\varepsilon}{3s'}\Bigr)^{-1/2}\le\Bigl(1-\frac{\varepsilon}{3s'}+\frac{\varepsilon^2}{6s'^2}\Bigr)\exp\Bigl(-\frac{\varepsilon^2v_n(s')}{24n}\Bigr).$$
--
--   It bounds the factor $(1+2\varepsilon/(3s'))^{-1/2}$ of (2.7) in the proof of Proposition 1.
--
--   **Formalization Note** Two deliberate departures from the printed (2.8). (1) The page prints the factor $1-\varepsilon^2/(3s')+\varepsilon/(6s'^2)$, with the numerators swapped; the proof applies Claim 1 with $x=\varepsilon/(3s')$, which gives $1-x+3x^2/2=1-\varepsilon/(3s')+\varepsilon^2/(6s'^2)$, the factor of (2.5). The corrected factor is stated. (2) The hypothesis $\varepsilon\le3s'$ (that is, $x\in[0,1]$, the range of Claim 1) is added: without it the corrected claim is false (for $n=9$, $n\varepsilon=9$, $ns'=1$ the left side is about $0.378$ and the right side about $0.128$). In the only use, Proposition 1, $s'=1-2\varepsilon/3-j/n>\varepsilon/3$, so the hypothesis holds there.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1276, Claim 2, (2.8)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem claim_2 (n : ℕ) (hn : 1 ≤ n) (ε s' : ℝ) (hε : 0 < ε) (hs' : 0 < s')
    (hnε : 2 ≤ (n : ℝ) * ε) (hns' : 1 ≤ (n : ℝ) * s') (hx : ε ≤ 3 * s') :
    (1 + 2 * ε / (3 * s')) ^ (-(1 / 2 : ℝ)) ≤
      (1 - ε / (3 * s') + ε ^ 2 / (6 * s' ^ 2)) * Real.exp (-(ε ^ 2 * v n s') / (24 * (n : ℝ))) := by sorry

end MassartDKW.Tight
