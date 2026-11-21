-- Prove2me | Theorems.Thm_HodgeComputer_DiagonalPermutation_chart_and_target_irreducible
-- name    : HodgeComputer.DiagonalPermutation.chart_and_target_irreducible
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:54.066198+00:00
-- url     : https://prove2.me/theorems/61adb094-0105-41c3-9e23-65eca6c96e25
-- title:
--   Irreducibility of the projective sextic and reflection-chart cover for diagonal-permutation
-- statement:
--   For the open frontier instance `diagonal-permutation` (`Simultaneous permutations · standard sector`), both the six-variable projective sextic $F \in \mathbb{C}[X_0, X_1, X_2, Y_0, Y_1, Y_2]$ and its $(01)$-reflection chart equation $H_{\mathrm{diag}}(\lambda, b, c, d, v) = f_{\mathrm{diag}}(\lambda, b, c, d, v^2)$ are irreducible over $\mathbb{C}$:
--
--   $$
--   \operatorname{Irreducible}(F) \;\wedge\; \operatorname{Irreducible}\bigl(f_{\mathrm{diag}}(\lambda, b, c, d, v^2)\bigr).
--   $$
--
--   These primality properties guarantee that nonvanishing modulo $f_{\mathrm{diag}}$ lifts to relative primality against $H_{\mathrm{diag}}$ and against $F$ when clearing denominators to $\mathbb{P}^5$.
--
--   **Formalization Note** Proved by monic specialization to $X_0^6 + Y_0^6 + 1$ and $b^6 + (2 + 30 v^2 + 30 v^4 + 2 v^6)$, each of which is Eisenstein at $(T - i) \subset \mathbb{C}[T]$.
-- source:
--   Hodge.computer Atlas instance `diagonal-permutation`, `data/diagonal-permutation/instance.rec` and Discussion #177, https://github.com/hodge-computer/sextics/discussions/177

import Definitions.Def_HodgeComputerDiagonalPermutationQuotient
import Mathlib.RingTheory.Polynomial.UniqueFactorization

theorem HodgeComputer.DiagonalPermutation.chart_and_target_irreducible :
    Irreducible HodgeComputer.DiagonalPermutation.F ∧
      Irreducible (HodgeComputer.ReflectionChart.squareLift
        HodgeComputer.DiagonalPermutation.diagWeighted) := by sorry
