-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_eq_7
-- name    : GilesMLMC.Complexity.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:50.647801+00:00
-- url     : https://prove2.me/theorems/a3c13f83-020d-4114-b2ef-95292b406203
-- title:
--   (7) — $\sum_{l=0}^Lh_l^{-1}<\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha}\varepsilon^{-2}$
-- statement:
--   Let $M\ge2$ be an integer, $T>0$, $\alpha\ge\frac12$, $c_1>0$ and $0<\varepsilon<e^{-1}$, and let $L\ge0$ be the level chosen in (6), $L=\lceil\log(\sqrt2c_1T^\alpha\varepsilon^{-1})/(\alpha\log M)\rceil$. With $h_l=M^{-l}T$,
--   $$\sum_{l=0}^{L}h_l^{-1}<\frac{M^2}{M-1}\,(\sqrt2\,c_1)^{1/\alpha}\,\varepsilon^{-2}.$$
--
--   This bounds the cost of the single extra sample per level that the ceilings in $N_l$ add, uniformly in the three cases of the proof.
--
--   **Formalization Note** The level $L$ is the natural number equal to the paper's integer ceiling in (6); this encodes that the ceiling is nonnegative, which the proof assumes silently (for a negative ceiling there is no estimator $\sum_{l=0}^L$). $\varepsilon>0$ is implicit in "$\varepsilon<e^{-1}$".
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, (7), p. 609

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Inequality (7) (Giles 2008, §3, proof of Theorem 3.1, p. 609, PDF 3, right column): `Σ_{l=0}^L h_l⁻¹ < M²/(M−1) (√2 c₁)^{1/α} ε⁻²`.

Formalization Note. The level `L` is the paper's choice (6), taken as a natural number: `(L : ℤ) = Lchoice …` encodes that the integer ceiling is nonnegative, which the proof assumes silently (for a negative ceiling there is no estimator `Σ_{l=0}^L`). `ε > 0` is implicit in "ε < e⁻¹". `ε⁻²` is the real power `ε ^ (-2 : ℝ)`. -/
theorem eq_7
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ <
      (M : ℝ) ^ 2 / ((M : ℝ) - 1) * (Real.sqrt 2 * c₁) ^ (1 / α) * ε ^ (-2 : ℝ) := by sorry

end GilesMLMC.Complexity
