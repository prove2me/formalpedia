-- Prove2me | Theorems.Thm_LL_Decomp1535a_ternaryAbove_of_arcs
-- name    : LL_Decomp1535a.ternaryAbove_of_arcs
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:19:40.695987+00:00
-- url     : https://prove2.me/theorems/80a91ada-d9e5-4365-bdcc-b3a0afc21b0b
-- title:
--   Major and minor arc bounds give every odd N at least C as a sum of three primes
-- statement:
--   Let $C$ be real. Suppose that for every odd natural number $N\ge C$ there are a measurable set $M\subseteq\mathbb R$ and reals $A$, $B$ with $B\ge0$, $A\le\operatorname{Re}\int_{(0,1]\cap M}F_N(\alpha)\,d\alpha$, $|S_N(\alpha)|\le B$ for every $\alpha\in(0,1]\setminus M$, and $B\cdot\log N\cdot(\log 4\cdot N)<A$. Then every odd natural number $n\ge C$ is a sum of three primes.
-- source:
--   Liu and Wang 2002, Section 3, pp. 145 to 146, the circle method route of eqs. 3.9 and 3.10

import Mathlib
import Definitions.Def_LL_Decomp1535a_IsTernarySum
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F
import Definitions.Def_LL_Decomp1535a_TernaryAbove

open MeasureTheory

namespace LL_Decomp1535a
theorem ternaryAbove_of_arcs {C : ℝ}
    (h : ∀ N : ℕ, Odd N → C ≤ N → ∃ M : Set ℝ, MeasurableSet M ∧ ∃ A B : ℝ, 0 ≤ B ∧
      A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α).re ∧
      (∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) ∧
      B * (Real.log N * (Real.log 4 * N)) < A) :
    TernaryAbove C := by sorry
end LL_Decomp1535a
