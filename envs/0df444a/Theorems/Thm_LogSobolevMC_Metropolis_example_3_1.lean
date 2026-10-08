-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_3_1
-- name    : LogSobolevMC.Metropolis.example_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:57.02397+00:00
-- url     : https://prove2.me/theorems/510d5282-75bd-48d4-8ac7-c9581d572b3c
-- title:
--   Example 3.1, p. 715 — the two-point chain has π ≡ 1/2, λ = 2 and α = λ/2 = 1
-- statement:
--   Consider the two-point space $\mathcal X=\{-1,1\}$ with kernel $K(-1,1)=K(1,-1)=1$ (and $K(-1,-1)=K(1,1)=0$). Its stationary measure is $\pi\equiv 1/2$, its spectral gap is $\lambda=2$, and its log-Sobolev constant is
--
--   $$\alpha=\frac{\lambda}{2}=1.$$
--
--   The two-point chain is the building block of the hypercube walk (Example 3.2); it shows that the inequality $2\alpha\le\lambda$ of Lemma 3.1 is sharp.
--
--   **Formalization Note** $\{-1,1\}$ is encoded as `Fin 2`; $\lambda$ and $\alpha$ are the variational infima of the mission's `Setting`.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 715, Example 3.1

import Mathlib
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.1, p. 715: the two-point chain `K(−1, 1) = K(1, −1) = 1` on `{−1, 1}` has
stationary measure `π ≡ 1/2`, spectral gap `λ = 2` and log-Sobolev constant `α = λ/2 = 1`. -/
theorem example_3_1 :
    MarkovMixing.IsStationary swap2 (fun _ => (1 / 2 : ℝ)) ∧
    LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) = 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) / 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = 1 := by sorry

end LogSobolevMC.Metropolis
