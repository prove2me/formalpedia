-- Prove2me | Theorems.Thm_Komlos_beck_fiala
-- name    : Komlos.beck_fiala
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-03T20:51:18.771905+00:00
-- url     : https://prove2.me/theorems/9c881776-bf78-4290-8398-b046bec30e9c
-- title:
--   The Beck--Fiala theorem: discrepancy at most $2t-1$
-- statement:
--   (Beck--Fiala 1981.) Let $A$ be an $m \times n$ matrix with entries in $\{0, 1\}$ — the incidence matrix of $m$ sets over $n$ elements — in which every column has at most $t \ge 1$ ones: every element belongs to at most $t$ sets. Then there are signs $\varepsilon_j \in \{\pm 1\}$ with
--   $$\Big|\sum_{j=1}^{n} A_{ij}\,\varepsilon_j\Big| \le 2t - 1 \qquad \text{for every set } i.$$
--   The bound depends only on the degree $t$, not on $m$ or $n$. The hypothesis $t \ge 1$ is necessary for the formal statement (a degree-$0$ system has discrepancy $0$, but $2t-1$ would be $-1$).
-- source:
--   Beck--Fiala, "Integer-making" theorems, Discrete Applied Mathematics 3 (1981) 1-8, Theorem: disc at most 2t-1 for degree-t set systems, https://doi.org/10.1016/0166-218X(81)90022-6

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem beck_fiala (t n m : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 2 * (t : ℝ) - 1 := by sorry

end Komlos
