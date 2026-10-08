-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_interval0_roots_card_le
-- name    : OAI.InternalCatalan.barrierCase2AX_interval0_roots_card_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T20:45:00.025252+00:00
-- url     : https://prove2.me/theorems/eb103769-4509-4cc6-b424-b92782a13fe7
-- title:
--   OpenAI Catalan, §7.2 Eq. (94) — the derivative numerator A_X has at most nine roots in (−1, 0)
-- statement:
--   Let $A_X\in\mathbb Q[x]$ be the derivative numerator of the case-$\kappa=2$ barrier function $X_2$ (`barrierCase2AX`, bundle `OAICatalanBarrierPolynomials`). Every finite set $s$ of real numbers in $(-1,0)$ at which $A_X$ vanishes has at most nine elements:
--
--   $$|s|\le 9\qquad\text{whenever } s\subseteq(-1,0)\text{ and }A_X(x)=0\text{ for all }x\in s.$$
--
--   This is the sign-variation bound of the root table on p. 37 for $\kappa=2$, function $X$, on the division interval $(-1,0)$ (variation count $9$): after the substitution of Eq. (94) the transformed coefficients have nine sign changes, and Descartes' rule of signs bounds the number of roots, counted with multiplicity.
--
--   OpenAI, p. 37: “Delete zero coefficients and count consecutive sign changes. The degrees and the resulting counts, in the order of the consecutive intervals, are … $\kappa=2$, $X$, $d_0=36$, division points $-1,0,1$, sign variations $9,9$.”
--
--   **Formalization note.** The bound is stated for finite sets of roots (so it bounds the number of distinct roots). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 37, root table (κ = 2, X, interval (-1,0), 9 sign variations) and Eq. (94)

import Mathlib
import Definitions.Def_OAICatalanIrrationality
import Definitions.Def_OAICatalanBarrierPolynomials

namespace OAI.InternalCatalan

open Polynomial

theorem barrierCase2AX_interval0_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 9 := by
  sorry

end OAI.InternalCatalan
