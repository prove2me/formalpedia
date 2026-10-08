-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_3_3_compare
-- name    : LogSobolevMC.Metropolis.example_3_3_compare
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:06.092908+00:00
-- url     : https://prove2.me/theorems/0ca2bc81-e30b-4aae-a8fc-48d4c942e8f8
-- title:
--   Example 3.3, p. 719 — ½P(x, y) ≤ M(x, y) ≤ P(x, y) for x ≠ y, hence ℰ_M ≤ ℰ_P ≤ 2ℰ_M
-- statement:
--   Fix $n\ge 1$, let $M$ be the Metropolis chain (1.9) and $P$ the Ehrenfest chain on $\{0,\dots,n\}$, and $\pi(x)=2^{-n}\binom nx$. Then
--
--   $$\tfrac12P(x,y)\le M(x,y)\le P(x,y)\qquad (x\ne y),$$
--
--   and consequently the Dirichlet forms with respect to $\pi$ satisfy
--
--   $$\mathcal E_M(f,f)\le\mathcal E_P(f,f)\le 2\,\mathcal E_M(f,f)\qquad\text{for all } f.$$
--
--   These are the hypotheses of the comparison Lemma 3.3 for the pair $(M,P)$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 719, Example 3.3

import Mathlib
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.3, p. 719 (comparison): the Metropolis chain `M` of (1.9) and the Ehrenfest
chain `P` satisfy `½P(x, y) ≤ M(x, y) ≤ P(x, y)` for `x ≠ y`, hence their Dirichlet forms
with respect to the binomial distribution satisfy `ℰ_M ≤ ℰ_P ≤ 2ℰ_M`. -/
theorem example_3_3_compare (n : ℕ) (hn : 1 ≤ n) :
    (∀ x y : Fin (n + 1), x ≠ y →
      1 / 2 * ehrenfest n x y ≤ binomMetropolis n x y ∧
        binomMetropolis n x y ≤ ehrenfest n x y) ∧
    (∀ f : Fin (n + 1) → ℝ,
      LogSobolevMC.ChiSquare.dirichlet (binomMetropolis n) (binomPi n) f f ≤ LogSobolevMC.ChiSquare.dirichlet (ehrenfest n) (binomPi n) f f ∧
        LogSobolevMC.ChiSquare.dirichlet (ehrenfest n) (binomPi n) f f ≤
          2 * LogSobolevMC.ChiSquare.dirichlet (binomMetropolis n) (binomPi n) f f) := by sorry

end LogSobolevMC.Metropolis
