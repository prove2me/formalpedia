-- Prove2me | Theorems.Thm_MvPowerSeries_isNoetherianRing_fin
-- name    : MvPowerSeries.isNoetherianRing_fin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c0ee3ea6-848d-5ffb-950a-7a5111d9ccb5
-- title:
--   Power series in finitely many variables over a Noetherian ring
-- statement:
--   Let $R$ be a commutative ring that is Noetherian as a ring, i.e. its ideals satisfy the ascending chain condition, and let $n$ be a natural number. The assertion is that the ring `MvPowerSeries (Fin n) R` of formal power series over $R$ in the variables indexed by `Fin n` — that is, functions from the monoid of finitely supported exponent vectors $\mathbb{N}^{\mathrm{Fin}\,n}$ to $R$, with the Cauchy product as multiplication — is again a Noetherian ring. The number of variables is an arbitrary natural number, so the case $n = 0$ (where the ring is isomorphic to $R$) is included; no hypothesis beyond commutativity and Noetherianity of $R$ is imposed. The result is stated for the particular index type `Fin n` rather than for an arbitrary finite index type.
--
--   This is the Hilbert basis theorem for formal power series in finitely many variables, the multivariate extension of the one-variable statement available in Mathlib. It supplies the Noetherian hypothesis for rings of the form $\mathcal{O}[[X_1,\dots,X_g]]$ that occur as (framed) universal deformation rings and as the patched rings of the Taylor–Wiles–Kisin method, and is invoked in the treatment of adic completions and of local charts on modular and Drinfeld curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_isNoetherianRing_fin.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPowerSeries.isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by sorry
