-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_case_b_complexity
-- name    : GilesMLMC.Complexity.case_b_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:33.495989+00:00
-- url     : https://prove2.me/theorems/87da6263-84f3-4e83-a156-23ab2a882bb0
-- title:
--   Case (b), $\beta>1$ — $C\le c_4\varepsilon^{-2}$ with $c_4=2c_3c_2T^{\beta-1}(1-M^{-(\beta-1)/2})^{-2}+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha}$
-- statement:
--   Let $M\ge2$ be an integer, $T>0$, $\alpha\ge\frac12$, $\beta>1$, $c_1,c_2,c_3>0$ and $0<\varepsilon<e^{-1}$. Let $C_l^{(n)}$ be the computational complexity of the level-$l$ estimator with $n$ samples, with
--
--   (iv) $C_l^{(n)}\le c_3\,n\,h_l^{-1}$ for every $l$ and $n\ge1$, where $h_l=M^{-l}T$.
--
--   Let $L\ge0$ be the level of (6) and $N_l$ the sample sizes of case (b). Then $C=\sum_{l=0}^LC_l^{(N_l)}$ satisfies
--   $$C\le c_4\,\varepsilon^{-2},\qquad c_4=2c_3c_2T^{\beta-1}\big(1-M^{-(\beta-1)/2}\big)^{-2}+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha}.$$
--
--   This is the cost half of the theorem in the case $\beta>1$: the cost is that of a single unbiased Monte Carlo estimate.
--
--   **Formalization Note** The complexity $C_l^{(n)}$ is abstract and constrained only by (iv). The level $L$ is the natural number equal to the paper's integer ceiling in (6); this encodes that the ceiling is nonnegative, which the proof assumes silently (for a negative ceiling there is no estimator $\sum_{l=0}^L$). $\varepsilon>0$ is implicit in "$\varepsilon<e^{-1}$".
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (b), complexity, p. 610

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Case (b) of the proof of Theorem 3.1, complexity (Giles 2008, §3, p. 610, PDF 4, left column): with the case (b) sample sizes, `C ≤ c₄ ε⁻²` where `c₄ = 2c₃c₂T^{β−1}(1 − M^{−(β−1)/2})^{−2} + c₃ M²/(M−1) (√2c₁)^{1/α}`.

Formalization Note. `cost l n` is the computational complexity C_l of the level-`l` estimator with `n` samples, constrained only by (iv) for every `n ≥ 1`; `C = Σ_{l=0}^L C_l` is `totalCost`. The level `L` is the paper's choice (6), taken as a natural number: `(L : ℤ) = Lchoice …` encodes that the integer ceiling is nonnegative, which the proof assumes silently (for a negative ceiling there is no estimator `Σ_{l=0}^L`). `ε > 0` is implicit in "ε < e⁻¹". -/
theorem case_b_complexity
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (cost : ℕ → ℕ → ℝ) (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    totalCost cost (NB M T β c₂ ε) L ≤ c₄B M T α β c₁ c₂ c₃ * ε ^ (-2 : ℝ) := by sorry

end GilesMLMC.Complexity
