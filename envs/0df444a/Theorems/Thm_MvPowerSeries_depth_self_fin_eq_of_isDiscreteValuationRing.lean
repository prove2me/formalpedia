-- Prove2me | Theorems.Thm_MvPowerSeries_depth_self_fin_eq_of_isDiscreteValuationRing
-- name    : MvPowerSeries.depth_self_fin_eq_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/9853622b-26bf-50cc-8971-de7197465acb
-- title:
--   Depth of 𝒪[[X₁,…,Xₙ]] over a discrete valuation ring
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is an integral domain and a discrete valuation ring, and let $n$ be a natural number. Put $\Lambda =$ `MvPowerSeries (Fin n) 𝓞`, the ring of formal power series over $\mathcal{O}$ in the $n$ variables indexed by `Fin n`; it is local, and the assertion concerns $\Lambda$ regarded as a module over itself. By definition, the depth in question is the supremum, taken in $\mathbb{N}\cup\{\infty\}$, of the lengths of those finite lists $s$ of elements of $\Lambda$ which form a weakly regular sequence on the $\Lambda$-module $\Lambda$ and all of whose entries lie in the maximal ideal of $\Lambda$. The theorem states that this supremum is exactly the natural number $n+1$, viewed as an element of $\mathbb{N}\cup\{\infty\}$; in particular it is finite, so no weakly regular sequence inside the maximal ideal has length exceeding $n+1$, while one of length $n+1$ exists.
--
--   This is the depth half of the statement that $\mathcal{O}[[X_1,\dots,X_n]]$ is Cohen–Macaulay of dimension $n+1$ when $\mathcal{O}$ is a discrete valuation ring, the sequence realising the bound being a uniformiser together with the variables. Paired with the computation of the Krull dimension of the same ring, it supplies the equality of depth and dimension that feeds the Auslander–Buchsbaum freeness criterion for modules over the patching ring, and it is used in the analysis of the finite free quotients arising from formal groups in several variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_depth_self_fin_eq_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing RingTheory

theorem MvPowerSeries.depth_self_fin_eq_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    Module.depth (MvPowerSeries (Fin n) 𝓞) (MvPowerSeries (Fin n) 𝓞) = ((n + 1 : ℕ) : ℕ∞) := by sorry
