-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_3_2
-- name    : LogSobolevMC.Metropolis.example_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:07.304985+00:00
-- url     : https://prove2.me/theorems/6534311d-1f86-4487-989e-09bb257b7aba
-- title:
--   Example 3.2, p. 717 — the hypercube walk is the product of two-point chains and has α = λ/2 = 1/n
-- statement:
--   Let $n\ge 1$ and consider the hypercube $\mathcal X=\{-1,1\}^n$ with $K(x,y)=1/n$ if $x,y$ differ at exactly one coordinate and $K(x,y)=0$ otherwise. Then the uniform measure $\pi\equiv 2^{-n}$ is stationary, $K$ is the product chain (2.9) of $n$ copies of the two-point chain of Example 3.1, and
--
--   $$\alpha=\frac{\lambda}{2}=\frac1n.$$
--
--   This is the first nontrivial chain whose log-Sobolev constant is known exactly; it is projected onto the Ehrenfest chain in Example 3.3.
--
--   **Formalization Note** $\{-1,1\}^n$ is `Fin n → Fin 2`.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 717, Example 3.2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.2, p. 717: on the hypercube `{−1, 1}ⁿ`, the chain `K(x, y) = 1/n` for `x, y`
differing at exactly one coordinate has the uniform stationary measure `π ≡ 2⁻ⁿ`, is the
product chain of the two-point chains of Example 3.1, and satisfies `α = λ/2 = 1/n`. -/
theorem example_3_2 (n : ℕ) (hn : 1 ≤ n) :
    MarkovMixing.IsStationary (hypercube n) (fun _ => (1 / 2 : ℝ) ^ n) ∧
    hypercube n = MarkovMixing.productChain (fun _ : Fin n => swap2) ∧
    LogSobolevMC.ChiSquare.logSobolev (hypercube n) (fun _ => (1 / 2 : ℝ) ^ n) =
      LogSobolevMC.ChiSquare.gap (hypercube n) (fun _ => (1 / 2 : ℝ) ^ n) / 2 ∧
    LogSobolevMC.ChiSquare.gap (hypercube n) (fun _ => (1 / 2 : ℝ) ^ n) / 2 = 1 / (n : ℝ) := by sorry

end LogSobolevMC.Metropolis
