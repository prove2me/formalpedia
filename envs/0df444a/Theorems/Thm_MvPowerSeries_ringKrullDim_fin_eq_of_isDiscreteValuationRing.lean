-- Prove2me | Theorems.Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
-- name    : MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/80c159f5-e9bd-5dfd-ba71-de65f6fa4926
-- title:
--   Krull dimension of 𝒪[[X₁,…,Xₙ]] over a discrete valuation ring
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is a domain and a discrete valuation ring (in the Mathlib sense: a local principal ideal domain that is not a field), and let $n$ be a natural number. The assertion is an equality in `WithBot ℕ∞`, the value group of `ringKrullDim`: the Krull dimension of the ring `MvPowerSeries (Fin n) 𝓞` of formal power series over $\mathcal{O}$ in the variables indexed by `Fin n`, i.e. of $\mathcal{O}[[X_0,\dots,X_{n-1}]]$, equals the image of the natural number $n+1$ under the coercion $\mathbb{N} \to$ `WithBot ℕ∞`. In particular the value is finite (neither $\bot$, which would signal the zero ring, nor $\top$), and for $n = 0$ the statement reduces to the fact that a discrete valuation ring has Krull dimension $1$. The index type is the concrete finite type `Fin n`, so the statement is about power series in a specified finite number of variables rather than in an arbitrary finite index set.
--
--   This is the standard computation $\dim \mathcal{O}[[X_1,\dots,X_n]] = n + 1$ for $\mathcal{O}$ a discrete valuation ring, the dimension-theoretic input to the numerology of the patching argument, where the rings $\mathcal{O}[[X_1,\dots,X_g]]$ and $\mathcal{O}[[y_1,\dots,y_r]]$ are compared. It is used in the project as a dimension count for power series rings over $\mathcal{O}$, and is cited by a number of downstream results in the algebraic-geometry and patching developments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) 𝓞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by sorry
