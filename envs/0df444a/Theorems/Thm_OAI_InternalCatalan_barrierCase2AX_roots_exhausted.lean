-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_roots_exhausted
-- name    : OAI.InternalCatalan.barrierCase2AX_roots_exhausted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T20:45:19.034207+00:00
-- url     : https://prove2.me/theorems/3ec19dad-5603-46dd-9bf3-699b12937b2b
-- title:
--   OpenAI Catalan, §7.2 — every root of the derivative numerator A_X in (−1, 0) ∪ (0, 1) lies in one of the eighteen root brackets
-- statement:
--   Let $A_X\in\mathbb Q[x]$ be the derivative numerator of the case-$\kappa=2$ barrier function $X_2$ (`barrierCase2AX`, bundle `OAICatalanBarrierPolynomials`) and let $\mathcal M_X$ be the eighteen integers of the root table for $X_2$ on p. 38 (`barrierCase2XBrackets`). For every real $x\in(-1,0)\cup(0,1)$ with $A_X(x)=0$ there is $m\in\mathcal M_X$ with
--
--   $$\frac{m}{10^{10}}<x<\frac{m+2}{10^{10}}.$$
--
--   This is the root-exhaustion certificate for $X_2$: on each division interval the number of sign variations after the substitution (94) bounds the number of roots (Descartes' rule of signs), each listed bracket contains a root by the sign check (95), and the counts agree.
--
--   OpenAI, p. 37: “The numbers of brackets in each consecutive interval equal the displayed variation counts. The intermediate value theorem and the variation bound therefore give exactly one simple root per bracket and no other roots in those open intervals.”
--
--   **Formalization note.** $A_X$ is evaluated at the real point $x$ after mapping its rational coefficients to $\mathbb R$. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 37-38, §7.2, Eq. (94)-(95) and the root table, κ = 2, function X

import Mathlib
import Definitions.Def_OAICatalanIrrationality
import Definitions.Def_OAICatalanBarrierPolynomials

namespace OAI.InternalCatalan

open Polynomial

theorem barrierCase2AX_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase2XBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  sorry

end OAI.InternalCatalan
