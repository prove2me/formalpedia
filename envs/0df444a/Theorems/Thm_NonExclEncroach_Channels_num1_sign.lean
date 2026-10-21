-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_num1_sign
-- name    : NonExclEncroach.Channels.num1_sign
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:39.648913+00:00
-- url     : https://prove2.me/theorems/f1d9a918-50b3-4436-b94d-1b486cb263ad
-- title:
--   Proof of Proposition 5, Online Technical Appendix p. 16 — Num1 is strictly decreasing, Num1(0.1) > 0 > Num1(1), and sign c2 = sign Num1
-- statement:
--   Let
--   $$\mathrm{Num1}(\theta)=32-\theta\Big(80+\theta\big(32+\theta(14+\theta(8-(4-\theta)\theta))\big)\Big).$$
--   Then
--   1. $\mathrm{Num1}$ is strictly decreasing on $[0,1]$;
--   2. $\mathrm{Num1}(0.1)>0$ and $\mathrm{Num1}(1)<0$;
--   3. for every $\theta\in(0,1)$, $c_2(\theta)>0$ if and only if $\mathrm{Num1}(\theta)>0$, and $c_2(\theta)<0$ if and only if $\mathrm{Num1}(\theta)<0$.
--
--   Consequently $\mathrm{Num1}$ has a unique root $\hat\theta_{12}\in(0,1)$ (numerically $\hat\theta_{12}\approx0.3443$), with $c_2>0$ below it and $c_2<0$ above it. This is the threshold of Proposition 5.
--
--   **Formalization Note** Item 3 uses that the denominator $2(1+\theta)(128-16\theta^2-13\theta^4)$ of $c_2$ is positive on $(0,1)$ and that the numerator of $c_2$ equals $\theta\,\mathrm{Num1}(\theta)$.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, Online Technical Appendix p. 16 (PDF 49), proof of Proposition 5; (A.5)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem num1_sign :
    StrictAntiOn num1 (Set.Icc 0 1) ∧ 0 < num1 (1 / 10) ∧ num1 1 < 0 ∧
      ∀ θ, 0 < θ → θ < 1 → (0 < c2 θ ↔ 0 < num1 θ) ∧ (c2 θ < 0 ↔ num1 θ < 0) := by sorry

end NonExclEncroach.Channels
