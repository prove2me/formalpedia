-- Prove2me | Theorems.Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing
-- name    : MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/7545cfb2-6353-5266-89ba-73f69aaef6f9
-- title:
--   Power series in finitely many variables over a noetherian ring
-- statement:
--   Let $R$ be a commutative ring in a fixed universe which is noetherian, i.e. its ideals satisfy the ascending chain condition (equivalently, $R$ is noetherian as a module over itself), and let $n$ be a natural number. The assertion is that the ring `MvPowerSeries (Fin n) R` of formal power series in the variables indexed by $\mathrm{Fin}\,n$ with coefficients in $R$ — that is, the ring of functions from finitely supported maps $\mathrm{Fin}\,n \to \mathbb{N}$ to $R$, with convolution product — is again a noetherian ring. The index type is restricted to the standard finite types $\mathrm{Fin}\,n$; no statement is made for power series in an arbitrary finite, or infinite, set of variables, and $n = 0$ is allowed (the power series ring is then isomorphic to $R$).
--
--   This is the several-variable form of the Hilbert basis theorem for formal power series, extending the one-variable statement available in Mathlib for $R[\![X]\!]$ to $R[\![x_1,\dots,x_n]\!]$. It serves as a basic finiteness input for the commutative algebra of formal deformation rings and of formal modules, and is cited by the results on formal $\mathcal{O}_D$-modules used in the Čerednik–Drinfeld part of the development, as well as by further statements about ideals and spans in multivariable power series rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by sorry
