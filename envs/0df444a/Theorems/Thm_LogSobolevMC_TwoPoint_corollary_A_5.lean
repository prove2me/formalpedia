-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_corollary_A_5
-- name    : LogSobolevMC.TwoPoint.corollary_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:45.801355+00:00
-- url     : https://prove2.me/theorems/7d641126-480f-45b1-a7d4-425435477248
-- title:
--   Corollary A.5, pp. 747–748 — the complete graph has α = (|𝒳| − 2)/((|𝒳| − 1) log(|𝒳| − 1)); ℤ₃ has α = 1/(2 log 2)
-- statement:
--   On a finite set $\mathcal X$ with $|\mathcal X|\ge3$, consider the Markov kernel $K(x,y)=1/(|\mathcal X|-1)$ for $x\ne y$ and $K(x,x)=0$ (simple random walk on the complete graph). It has stationary measure $\pi\equiv1/|\mathcal X|$, and its log-Sobolev constant is
--
--   $$\alpha=\frac{|\mathcal X|-2}{(|\mathcal X|-1)\log(|\mathcal X|-1)}.$$
--
--   In particular, the simple random walk on $\mathbb Z_3$ (step $\pm1$ with probability $1/2$ each) has log-Sobolev constant $\alpha=1/(2\log2)$.
--
--   Together with $\lambda=|\mathcal X|/(|\mathcal X|-1)$, this exhibits chains for which $\alpha<\lambda/2$.
--
--   **Formalization Note** The hypothesis $|\mathcal X|\ge3$ is added and disclosed: at $|\mathcal X|=2$ the formula reads $0/(1\cdot\log1)$, which Lean evaluates to $0$, while the true value is $1$ (Example 3.1). The random walk on $\mathbb Z_3$ is the published `MarkovMixing.cycleWalk 3` on `ZMod 3`, with the uniform measure `MarkovMixing.uniformDist`.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 747–748, Corollary A.5

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_spectral
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Corollary A.5 (pp. 747–748): on a finite set with `|𝒳| ≥ 3`, the kernel `K(x, y) = 1/(|𝒳| − 1)`
for `x ≠ y`, `K(x, x) = 0` has stationary measure `π ≡ 1/|𝒳|` and log-Sobolev constant
`(|𝒳| − 2)/((|𝒳| − 1) log(|𝒳| − 1))`; the simple random walk on `ℤ₃` has `α = 1/(2 log 2)`. -/
theorem corollary_A_5 :
    (∀ (V : Type) [Fintype V] [DecidableEq V], 3 ≤ Fintype.card V →
      IsStationary (completeChain V) (uniformDist V) ∧
        LogSobolevMC.ChiSquare.logSobolev (completeChain V) (uniformDist V) =
          ((Fintype.card V : ℝ) - 2) /
            (((Fintype.card V : ℝ) - 1) * Real.log ((Fintype.card V : ℝ) - 1))) ∧
    LogSobolevMC.ChiSquare.logSobolev (cycleWalk 3) (uniformDist (ZMod 3)) = 1 / (2 * Real.log 2) := by sorry

end LogSobolevMC.TwoPoint
