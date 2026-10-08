-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_knapsack_dp_recursion
-- name    : GilmoreGomory61.CuttingStock.knapsack_dp_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:11:16.960013+00:00
-- url     : https://prove2.me/theorems/48814514-f553-4de2-8fd4-5126519efc41
-- title:
--   p. 853 — dynamic programming recursion for F_s
-- statement:
--   For the first $s+1$ piece lengths, with the new type indexed $s$ in zero-based notation, the knapsack value obeys
--
--   $$
--   F_{s+1}(x)=\max_{0\le r\le\lfloor x/\ell_s\rfloor}\bigl(r b_s+F_s(x-r\ell_s)\bigr).
--   $$
--
--   The finite range for $r$ is the paper's bound on the number of pieces of the new type. This relation is the dynamic programming computation used to test pricing for the available stock lengths.
--
--   **Formalization Note** The source uses one-based $F_{s+1}$ with new length $\ell_{s+1}$; Lean's new type has index $s$. The statement requires positive lengths through this type. Earlier positive lengths are needed for the displayed finite range when negative capacities are permitted by the formal type. At $x<0$, both sides are $-\infty$.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 853, recursion for F_{s+1}

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack

namespace GilmoreGomory61.CuttingStock

/-- The Fₛ recursion and its finite range from p. 853. Earlier lengths must be positive too. -/
theorem knapsack_dp_recursion {m k : ℕ} (I : Instance m k)
    (b : Fin m → ℝ) (s : ℕ) (hs : s < m)
    (hℓ : ∀ i : Fin m, i.val ≤ s → 0 < I.ℓ i) (x : ℝ) :
    knapF I b (s + 1) x =
      ⨆ r ∈ Finset.range (⌊x / I.ℓ ⟨s, hs⟩⌋₊ + 1),
        (((r : ℝ) * b ⟨s, hs⟩ : ℝ) : EReal) +
          knapF I b s (x - r * I.ℓ ⟨s, hs⟩) := by sorry

end GilmoreGomory61.CuttingStock
