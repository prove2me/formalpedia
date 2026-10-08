-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_eq_6
-- name    : GilesMLMC.Complexity.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:16.959984+00:00
-- url     : https://prove2.me/theorems/12b88ff0-152f-44f8-8188-88d013231819
-- title:
--   (6) — the choice of $L$ gives $\tfrac1{\sqrt2}M^{-\alpha}\varepsilon<c_1h_L^\alpha\le\tfrac1{\sqrt2}\varepsilon$
-- statement:
--   Let $M\ge2$ be an integer and $T,\alpha,c_1,\varepsilon>0$. Choose the integer
--   $$L=\left\lceil \frac{\log(\sqrt2\,c_1T^\alpha\varepsilon^{-1})}{\alpha\log M}\right\rceil$$
--   and let $h_L=M^{-L}T$. Then
--   $$\frac1{\sqrt2}M^{-\alpha}\varepsilon< c_1h_L^\alpha\le\frac1{\sqrt2}\varepsilon .$$
--
--   The right inequality makes the bias at level $L$ at most $\varepsilon/\sqrt2$; the left one bounds $h_L^{-1}$, and hence the number of levels and the cost.
--
--   **Formalization Note** The statement holds for every value of the ceiling, including a negative one, so $L$ is an integer and $h_L$ uses an integer power. $\varepsilon>0$ is implicit in the paper.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, (6), p. 609

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Inequality (6) (Giles 2008, §3, proof of Theorem 3.1, p. 609, PDF 3, right column, top): with `L = ⌈log(√2 c₁ T^α ε⁻¹)/(α log M)⌉`, `(1/√2) M^{-α} ε < c₁ h_L^α ≤ (1/√2) ε`.

Formalization Note. Here `L` is the integer `Lchoice M T α c₁ ε` (`Int.ceil`), and `h_L = T M^{-L}` is `hz` (an integer power), so the statement holds for every value of the ceiling, including a negative one. Powers with real exponents are `Real.rpow`. `ε > 0` is implicit in the paper. -/
theorem eq_6
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    (M : ℝ) ^ (-α) * ε / Real.sqrt 2 < c₁ * hz M T (Lchoice M T α c₁ ε) ^ α ∧
      c₁ * hz M T (Lchoice M T α c₁ ε) ^ α ≤ ε / Real.sqrt 2 := by sorry

end GilesMLMC.Complexity
