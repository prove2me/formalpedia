-- Prove2me | Theorems.Thm_OpenGA_SurgeryVolumeProfile_surgeryTimes_finite
-- name    : OpenGA.SurgeryVolumeProfile.surgeryTimes_finite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T18:33:17.608913+00:00
-- url     : https://prove2.me/theorems/ddb13a1e-0ca6-4e25-adcf-7d4ab493bb2b
-- title:
--   Volume considerations rule out an accumulation of surgery times
-- statement:
--   Let $[a,b]$ be a compact time interval with $a\le b$, and let $P$ be a surgery volume profile on it: pre- and post-surgery volume functions $V^-,V^+$ with $V^+\ge 0$ on $[a,b]$, a set $S\subseteq(a,b]$ of surgery times, a growth rate $C\ge 0$ and a surgery scale $h>0$ satisfying
--   $$V^-(t)\le V^+(s)\,e^{C(t-s)}\quad (a\le s<t\le b),\qquad V^+(t)+h^3\le V^-(t)\quad (t\in S).$$
--
--   Then the set of surgery times is finite:
--   $$\#S<\infty .$$
--
--   This is the formal content of the phrase "volume considerations rule out an accumulation of surgery times" in Kleiner–Lott's outline of the proof of all-time existence for the Ricci flow with $(r,\delta)$-cutoff (p. 147). The two hypotheses are the volume growth estimate along the flow and the definite volume loss at a surgery of Remark 73.5. Quantitatively the argument bounds the number of surgeries on $[a,b]$ by
--   $$\frac{V^+(a)\,e^{C(b-a)}}{h^3},$$
--   since the discounted volume $U(t)=V^+(t)e^{-C(t-a)}$ is nonnegative and drops by at least $h^3e^{-C(b-a)}$ at every surgery.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Remark 73.5 (p. 140) and Section 77, p. 147

import Definitions.Def_OpenGA_SurgeryVolumeProfile

set_option autoImplicit false
open Set

theorem OpenGA.SurgeryVolumeProfile.surgeryTimes_finite {a b : ℝ}
    (P : OpenGA.SurgeryVolumeProfile a b) (hab : a ≤ b) :
    P.surgeryTimes.Finite := by sorry
