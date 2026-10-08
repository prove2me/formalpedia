-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_case_a_complexity
-- name    : GilesMLMC.Complexity.case_a_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:30.458071+00:00
-- url     : https://prove2.me/theorems/21bea307-dec7-469b-af97-c9357e4263a6
-- title:
--   Case (a), $\beta=1$ — $C\le c_4\varepsilon^{-2}(\log\varepsilon)^2$ with $c_4=2c_3c_5^2c_2+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha}$
-- statement:
--   Let $M\ge2$ be an integer, $T>0$, $\alpha\ge\frac12$, $c_1,c_2,c_3>0$ and $0<\varepsilon<e^{-1}$. For every level $l$ and sample size $n\ge1$ let $C_l^{(n)}$ be the computational complexity of the level-$l$ estimator with $n$ samples, and assume
--
--   (iv) $C_l^{(n)}\le c_3\,n\,h_l^{-1}$ for every $l$ and $n\ge1$, where $h_l=M^{-l}T$.
--
--   Let $L\ge0$ be the level of (6) and $N_l=\lceil2\varepsilon^{-2}(L+1)c_2h_l\rceil$. Then the total complexity $C=\sum_{l=0}^LC_l^{(N_l)}$ satisfies
--   $$C\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2,\qquad c_4=2c_3c_5^2c_2+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha},$$
--   with $c_5$ as in the bound $L+1\le c_5\log\varepsilon^{-1}$.
--
--   This is the cost half of the theorem in the case $\beta=1$.
--
--   **Formalization Note** The complexity $C_l^{(n)}$ is abstract and constrained only by (iv); $C$ is the sum of the level complexities. The level $L$ is the natural number equal to the paper's integer ceiling in (6); this encodes that the ceiling is nonnegative, which the proof assumes silently (for a negative ceiling there is no estimator $\sum_{l=0}^L$). $\varepsilon>0$ is implicit in "$\varepsilon<e^{-1}$".
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (a), complexity, p. 610

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Case (a) of the proof of Theorem 3.1, complexity (Giles 2008, §3, p. 610, PDF 4, left column, top): with `N_l = ⌈2ε⁻²(L+1)c₂h_l⌉`, `C ≤ c₄ ε⁻²(log ε)²` where `c₄ = 2c₃c₅²c₂ + c₃ M²/(M−1) (√2c₁)^{1/α}`.

Formalization Note. `cost l n` is the computational complexity C_l of the level-`l` estimator with `n` samples, constrained only by (iv) for every `n ≥ 1`; `C = Σ_{l=0}^L C_l` is `totalCost`. The level `L` is the paper's choice (6), taken as a natural number: `(L : ℤ) = Lchoice …` encodes that the integer ceiling is nonnegative, which the proof assumes silently (for a negative ceiling there is no estimator `Σ_{l=0}^L`). `ε > 0` is implicit in "ε < e⁻¹". -/
theorem case_a_complexity
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (cost : ℕ → ℕ → ℝ) (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    totalCost cost (NA M T c₂ ε L) L ≤ c₄A M T α c₁ c₂ c₃ * ε ^ (-2 : ℝ) * Real.log ε ^ 2 := by sorry

end GilesMLMC.Complexity
