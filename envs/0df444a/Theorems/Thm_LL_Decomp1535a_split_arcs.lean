-- Prove2me | Theorems.Thm_LL_Decomp1535a_split_arcs
-- name    : LL_Decomp1535a.split_arcs
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:11:16.714392+00:00
-- url     : https://prove2.me/theorems/45a98224-b7ab-4e1c-9381-126d7de58e1f
-- title:
--   Splitting the circle integral
-- statement:
--   For every natural number $N$ and every measurable set $M \subseteq \mathbb{R}$, $\int_{(0,1]} F_N=\int_{(0,1]\cap M} F_N+\int_{(0,1]\setminus M} F_N$.
-- source:
--   Liu and Wang 2002, p. 145, eqs. 3.11 and 3.12

import Mathlib
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F

open MeasureTheory

namespace LL_Decomp1535a
theorem split_arcs (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in Set.Ioc (0 : ℝ) 1, F N α =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α) + ∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α := by sorry
end LL_Decomp1535a
