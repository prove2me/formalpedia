-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_3_4
-- name    : LogSobolevMC.Metropolis.example_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:17.684241+00:00
-- url     : https://prove2.me/theorems/7d10ebd4-0686-4daf-880a-3eeb3e1d54a6
-- title:
--   Example 3.4, pp. 724–725 — M(x, x) ≥ 2/(n + 3), β_min ≥ −1 + 4/(n + 3), and ‖M_xˡ/π − 1‖₂ ≤ (1 + 2e²)^{1/2}e^{−c} for l ≥ (n/2)(log n + 2c) + 1
-- statement:
--   Fix $n\ge 1$, let $M$ be the Metropolis chain (1.9) on $\{0,\dots,n\}$ and $\pi(x)=2^{-n}\binom nx$. Then $M(x,x)\ge 2/(n+3)$ for all $x$, the smallest eigenvalue of $M$ satisfies $\beta_{\min}\ge -1+4/(n+3)$, and for every $c>0$, every starting point $x$ and every integer $l$,
--
--   $$\Big\|\frac{M^l_x}{\pi}-1\Big\|_2\le(1+2e^2)^{1/2}e^{-c}\qquad\text{for } l\ge\frac n2(\log n+2c)+1,$$
--
--   where $M^l_x=M^l(x,\cdot)$ and the norm is in $\ell^2(\pi)$.
--
--   This is the chi-square form of the upper bound in Theorem 1.1.
--
--   **Formalization Note** The chi-square bound is stated for every $x$, as printed. The paper derives it from Corollary 3.8, which assumes $\pi(x)\le 1/e$; this fails at the central states for $n\le 4$, where the printed claim is not covered by the paper's derivation and remains part of what is to be proved.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 724–725, Example 3.4

import Mathlib
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.4, pp. 724–725: the Metropolis chain `M` of (1.9) satisfies `M(x, x) ≥ 2/(n + 3)`
for all `x`, `β_min ≥ −1 + 4/(n + 3)`, and
`‖M_xˡ/π − 1‖₂ ≤ (1 + 2e²)^{1/2} e^{−c}` for `l ≥ (n/2)(log n + 2c) + 1`, `c > 0`. -/
theorem example_3_4 (n : ℕ) (hn : 1 ≤ n) :
    (∀ x : Fin (n + 1), 2 / ((n : ℝ) + 3) ≤ binomMetropolis n x x) ∧
    -1 + 4 / ((n : ℝ) + 3) ≤ betaMin (binomMetropolis n) (binomPi n) ∧
    (∀ (c : ℝ), 0 < c → ∀ (x : Fin (n + 1)) (l : ℕ),
      (n : ℝ) / 2 * (Real.log n + 2 * c) + 1 ≤ (l : ℝ) →
      LogSobolevMC.ChiSquare.lpNorm (binomPi n) 2 (fun y => (binomMetropolis n ^ l) x y / binomPi n y - 1) ≤
        Real.sqrt (1 + 2 * Real.exp 2) * Real.exp (-c)) := by sorry

end LogSobolevMC.Metropolis
