-- Prove2me | Theorems.Thm_FournierGuillin_Moment_step_1
-- name    : FournierGuillin.Moment.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:00.988222+00:00
-- url     : https://prove2.me/theorems/233807af-d2e1-4437-907b-b1375398f0be
-- title:
--   Step 1, proof of Theorem 1, p. 8 — Σ_{ℓ≥0} 2^{−pℓ} min{ε, 2^{dℓ/2}(ε/N)^{1/2}} ≤ C × (three regimes)
-- statement:
--   Let $d\ge1$ and $p>0$. There is a constant $C$, depending only on $p$ and $d$, such that for all $\varepsilon\in(0,1]$ and all integers $N\ge1$,
--   $$\sum_{\ell\ge0}2^{-p\ell}\min\Big\{\varepsilon,\,2^{d\ell/2}(\varepsilon/N)^{1/2}\Big\}\le C\times\begin{cases}\min\{\varepsilon,(\varepsilon/N)^{1/2}\}&\text{if }p>d/2,\\ \min\{\varepsilon,(\varepsilon/N)^{1/2}\log(2+\varepsilon N)\}&\text{if }p=d/2,\\ \min\{\varepsilon,\varepsilon(\varepsilon N)^{-p/d}\}&\text{if }p\in(0,d/2).\end{cases}$$
--
--   This sums the scale series of display (4) inside one shell, with $\varepsilon=2^{-qn}$ playing the role of the shell's mass; it is where the three regimes of Theorem 1 first appear.
--
--   **Formalization Note** The page states Step 1 "for all $\varepsilon\in(0,1)$" but applies it with $\varepsilon=2^{-qn}$, which equals $1$ at $n=0$; it is stated here for $\varepsilon\in(0,1]$, and the page's argument is unchanged. $C$ is chosen before $\varepsilon$ and $N$. The series is summed in $[0,\infty]$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proof of Theorem 1, Step 1, p. 8

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Step 1 of the proof of Theorem 1, p. 8: there is `C` (depending only on `p, d`) such that for all
`ε ∈ (0, 1]` and `N ≥ 1`, `Σ_{ℓ≥0} 2^{−pℓ} min{ε, 2^{dℓ/2}(ε/N)^{1/2}} ≤ C · rateStep1 d p ε N`.
The page states `ε ∈ (0, 1)` but applies it with `ε = 2^{−qn}`, which is `1` at `n = 0`. -/
theorem step_1 {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      ∑' ℓ : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(p * ℓ)) * min ε ((2 : ℝ) ^ ((d : ℝ) * ℓ / 2) * (ε / N) ^ (1 / 2 : ℝ)))
        ≤ ENNReal.ofReal (C * rateStep1 d p ε N) := by sorry

end FournierGuillin.Moment
