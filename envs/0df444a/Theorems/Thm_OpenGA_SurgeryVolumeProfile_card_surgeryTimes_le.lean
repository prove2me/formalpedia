-- Prove2me | Theorems.Thm_OpenGA_SurgeryVolumeProfile_card_surgeryTimes_le
-- name    : OpenGA.SurgeryVolumeProfile.card_surgeryTimes_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T18:48:01.439267+00:00
-- url     : https://prove2.me/theorems/f179efcc-57d5-4cdb-86f0-46793b0a54db
-- title:
--   Explicit bound on the number of surgeries on a finite time interval
-- statement:
--   Let $P$ be a surgery volume profile on a compact time interval $[a,b]$ with $a\le b$: pre- and post-surgery volume functions $V^-,V^+$ with $V^+\ge 0$ on $[a,b]$, a set $S\subseteq(a,b]$ of surgery times, a growth rate $C\ge 0$ and a surgery scale $h>0$ satisfying
--   $$V^-(t)\le V^+(s)e^{C(t-s)}\quad (a\le s<t\le b),\qquad V^+(t)+h^3\le V^-(t)\quad (t\in S).$$
--
--   Then the number of surgeries on the interval is bounded explicitly by the initial volume, the growth rate and the surgery scale:
--   $$\#S\cdot h^3\;\le\;V^+(a)\,e^{C(b-a)} .$$
--
--   This is the quantitative form of the statement that volume considerations rule out an accumulation of surgery times (Kleiner–Lott, p. 147): the volume available at time $a$ grows by at most the factor $e^{C(b-a)}$ over the interval, and every surgery consumes at least $h^3$ of it, as in Remark 73.5. Rearranged, the number of surgeries on $[a,b]$ is at most $V^+(a)e^{C(b-a)}/h^3$.
--
--   **Formalization note.** The cardinality is the natural-number cardinality of the set of surgery times, which is finite by the qualitative statement; the inequality is stated in the reals after coercion, and is therefore also meaningful, though weaker, in the form written above.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Remark 73.5 (p. 140) and Section 77, p. 147

import Definitions.Def_OpenGA_SurgeryVolumeProfile

set_option autoImplicit false
open Set

theorem OpenGA.SurgeryVolumeProfile.card_surgeryTimes_le {a b : ℝ}
    (P : OpenGA.SurgeryVolumeProfile a b) (hab : a ≤ b) :
    (P.surgeryTimes.ncard : ℝ) * P.surgeryScale ^ 3 ≤
      P.volAfter a * Real.exp (P.growthRate * (b - a)) := by sorry
