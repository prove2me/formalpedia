-- Prove2me | Theorems.Thm_Komlos_spencer_six_deviations
-- name    : Komlos.spencer_six_deviations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-03T20:52:05.343343+00:00
-- url     : https://prove2.me/theorems/85a762bf-e63c-4ed3-972a-edd93dd4a0c5
-- title:
--   Spencer: six standard deviations suffice
-- statement:
--   (Spencer 1985.) For any $n$ sets over $n$ elements — any $n \times n$ matrix $A$ with entries in $\{0,1\}$ — there are signs $\varepsilon_j \in \{\pm 1\}$ with
--   $$\Big|\sum_{j=1}^{n} A_{ij}\,\varepsilon_j\Big| \le 6\sqrt{n} \qquad \text{for every } i.$$
--   Random signs give $\Theta(\sqrt{n \log n})$; Spencer's theorem removes the logarithm, which no direct probabilistic argument can do. The constant $6$ is as in the original paper.
-- source:
--   Spencer, Six standard deviations suffice, Trans. Amer. Math. Soc. 289 (1985) 679-706, Theorem 1, https://doi.org/10.1090/S0002-9947-1985-0784009-0

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem spencer_six_deviations (n : ℕ) (A : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 6 * Real.sqrt n := by sorry

end Komlos
