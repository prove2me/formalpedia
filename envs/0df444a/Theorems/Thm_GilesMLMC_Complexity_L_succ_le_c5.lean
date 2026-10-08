-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_L_succ_le_c5
-- name    : GilesMLMC.Complexity.L_succ_le_c5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:41.260989+00:00
-- url     : https://prove2.me/theorems/f7f8ff50-50e4-4864-b3cf-d5016a87c43b
-- title:
--   Case (a) — $L+1\le c_5\log\varepsilon^{-1}$
-- statement:
--   Let $M\ge2$ be an integer, $T,\alpha,c_1>0$ and $0<\varepsilon<e^{-1}$. For the integer level $L=\lceil\log(\sqrt2c_1T^\alpha\varepsilon^{-1})/(\alpha\log M)\rceil$ of (6),
--   $$L+1\le c_5\log\varepsilon^{-1},\qquad c_5=\frac{1}{\alpha\log M}+\max\Big(0,\frac{\log(\sqrt2\,c_1T^\alpha)}{\alpha\log M}\Big)+2 .$$
--
--   The number of levels thus grows only logarithmically in $\varepsilon^{-1}$, with a constant independent of $\varepsilon$; in case (a) this is the source of the factor $(\log\varepsilon)^2$.
--
--   **Formalization Note** $L$ is the integer ceiling, cast to the reals; the bound holds whatever its sign. $\varepsilon>0$ is implicit in "$\varepsilon<e^{-1}$".
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (a), bound on L, p. 609

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Case (a) of the proof of Theorem 3.1, bound on `L` (Giles 2008, §3, p. 609, PDF 3, right column, bottom): for `ε < e⁻¹`, `L + 1 ≤ c₅ log ε⁻¹` with `c₅ = 1/(α log M) + max(0, log(√2 c₁ T^α)/(α log M)) + 2`.

Formalization Note. `L` is the integer ceiling `Lchoice M T α c₁ ε` of (6), cast to ℝ; the bound holds whatever its sign. `ε > 0` is implicit in "ε < e⁻¹". -/
theorem L_succ_le_c5
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ((Lchoice M T α c₁ ε : ℤ) : ℝ) + 1 ≤ c₅ M T α c₁ * Real.log ε⁻¹ := by sorry

end GilesMLMC.Complexity
