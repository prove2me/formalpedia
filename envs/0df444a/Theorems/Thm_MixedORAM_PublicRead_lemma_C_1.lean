-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_lemma_C_1
-- name    : MixedORAM.PublicRead.lemma_C_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T00:45:39.473197+00:00
-- url     : https://prove2.me/theorems/c36eca1d-6f57-4c3e-9faf-b7d34811e54c
-- title:
--   Lemma C.1 — uniform logarithmic inversion (reading: x > 0 and c > 0)
-- statement:
--   Let $c>0$. There is a constant $c'>0$ depending only on $c$ such that for all real $A\ge2$, $D\ge0$, $S>0$ and $x>0$,
--   $$x\log_2\Big(A+\frac Dx\Big)\ \ge\ cS\quad\Longrightarrow\quad x\ \ge\ \frac{c'S}{\log_2(A+D/S)} .$$
--
--   Applied with $x=R_N$, $A=2+r/p$, $D=Q$ and $S=H$, it turns (14) into $R_N=\Omega(G_p(Q))$.
--
--   Differences from the source:
--   - reading: x unrestricted → x > 0; reason: the proof works on x > 0 ('f is increasing for x > 0') and every use has x a positive cost; as printed the lemma is false for x < 0 (INSIGHTS I1)
--   - reading: a constant c (sign not stated) → c > 0; reason: c is the positive constant of Theorem A.1 in every use; for c ≤ 0 the hypothesis holds for every x > 0 and the lemma is false (INSIGHTS I2)
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 35, Lemma C.1

import Mathlib

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem lemma_C_1 (c : ℝ) (hc : 0 < c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ A D S x : ℝ, 2 ≤ A → 0 ≤ D → 0 < S → 0 < x →
      c * S ≤ x * Real.logb 2 (A + D / x) → c' * S / Real.logb 2 (A + D / S) ≤ x := by sorry

end MixedORAM.PublicRead
