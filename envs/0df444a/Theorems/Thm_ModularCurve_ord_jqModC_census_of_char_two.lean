-- Prove2me | Theorems.Thm_ModularCurve_ord_jqModC_census_of_char_two
-- name    : ModularCurve.ord_jqModC_census_of_char_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/1ea9105f-a117-53b0-a0a1-3ea467a26bb6
-- title:
--   Zeros of j on X₀(N) in characteristic 2: ramification census
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $2$ and let $N$ be a nonzero natural number whose image in $K$ is nonzero. Write $F =$ `modularFunctionFieldFullC K N` for the subfield of the Laurent series field $K((q))$ generated over $K$ by the elements `qExpand K d (jqModC K)` for the nonzero divisors $d$ of $N$, where `jqModC K` is $q^{-1}$ times the image in $K$ of the integral power series `jNum` $=$ `eisenstein4 ^ 3 * dedekindEtaUnitInv`; let $j \in F$ denote `jqModC K` itself. A place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$, and a principal ideal ring, and for such a place $P$ the integer $P.\mathrm{ord}(f)$ is minus the logarithm of the associated adic valuation of $f$. Let $S$ be a finite set of places of $F$ over $K$ such that a place lies in $S$ precisely when $P.\mathrm{ord}(j) > 0$. Then: (i) for every $P \in S$, $P.\mathrm{ord}(j) \in \{1,3,4,6,12\}$; (ii) $\#\{P \in S : \mathrm{ord} = 1\} + 3\,\#\{\mathrm{ord} = 3\} + 2\,\#\{\mathrm{ord} = 6\}$ equals `nuTwo N`, the number of $x \in \mathbb{Z}/N$ with $x^2 + 1 = 0$; (iii) $\#\{P \in S : \mathrm{ord} = 1\} + \#\{\mathrm{ord} = 4\}$ equals `nuThree N`, the number of $x \in \mathbb{Z}/N$ with $x^2 + x + 1 = 0$.
--
--   This is the census of the fibre of the map $j$ on the modular curve of full level-$N$ divisor type over the supersingular value $j = 0$ in characteristic $2$, with the possible ramification indices $1,3,4,6,12$ arising as the orbit sizes of the reduced automorphism group of the supersingular curve acting on the cyclic subgroups of order $N$, and the two weighted counts recording the subgroups fixed by automorphisms of order $2$ and $3$. It feeds the ramification bound [`ModularCurve.le_six_mul_sum_ordDiff_D_jqModC_of_lt_five`](thm.html#ModularCurve.le_six_mul_sum_ordDiff_D_jqModC_of_lt_five) used in the genus estimates for these curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jqModC_census_of_char_two.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_jqModC_census_of_char_two
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)) :
    (∀ P ∈ S, P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 4 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 12) ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      3 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3).card +
      2 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6).card =
      nuTwo N ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 4).card =
      nuThree N := by sorry
