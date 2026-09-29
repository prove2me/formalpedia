-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_abConvex_mono
-- name    : GallegoOzerADI.PositiveSetup.abConvex_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:46:22.850266+00:00
-- url     : https://prove2.me/theorems/ed38de47-6cff-4ef8-ba08-ec1e191ab699
-- title:
--   Lemma 1, Part 1 — $C(a,b) \subset C(a',b')$ for $(a,b) \le (a',b')$
-- statement:
--   Let $0 \le a \le a'$ and $0 \le b \le b'$. Every $(a,b)$-convex function is $(a',b')$-convex:
--
--   $$
--   C(a,b) \subset C(a',b').
--   $$
--
--   Enlarging the allowances $a, b$ in Definition 1 weakens the condition. The inclusion is used in the proof of Theorem 1 to pass from $C(0, \alpha_n K_n)$ to $C(0, K_{n-1})$ under the assumption $\alpha_n K_n \le K_{n-1}$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1349, Lemma 1, Part 1

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

namespace GallegoOzerADI.PositiveSetup

theorem abConvex_mono (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haa' : a ≤ a') (hbb' : b ≤ b')
    (g : ℝ → ℝ) (hg : ABConvex a b g) : ABConvex a' b' g := by sorry

end GallegoOzerADI.PositiveSetup
