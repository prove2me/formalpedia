-- Prove2me | Theorems.Thm_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ
-- name    : MvPowerSeries.exists_algEquiv_powerSeries_fin_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/515326d1-21db-5437-b1a1-a6809d26b3e0
-- title:
--   Splitting one variable off R[[X₀,…,Xₙ]]
-- statement:
--   Let $R$ be a commutative semiring and let $n$ be a natural number. The assertion is that there exists an $R$-algebra isomorphism $e$ from the ring $\mathrm{MvPowerSeries}\,(\mathrm{Fin}\,(n+1))\,R$ of formal power series in $n+1$ variables indexed by $\mathrm{Fin}\,(n+1)$ to the ring $\mathrm{PowerSeries}$ of formal power series in one variable over $\mathrm{MvPowerSeries}\,(\mathrm{Fin}\,n)\,R$, i.e. $R[[X_0,\dots,X_n]] \cong \bigl(R[[X_0,\dots,X_{n-1}]]\bigr)[[T]]$ as $R$-algebras, subject to two normalising conditions on the images of the variables: $e$ sends the variable $\mathrm{MvPowerSeries.X}\,0$, indexed by the zeroth element of $\mathrm{Fin}\,(n+1)$, to the one-variable indeterminate $\mathrm{PowerSeries.X}$; and for every $i$ in $\mathrm{Fin}\,n$, $e$ sends the variable indexed by the successor $i.\mathrm{succ}$ to the constant power series $\mathrm{PowerSeries.C}\,(\mathrm{MvPowerSeries.X}\,i)$, whose constant coefficient is the $i$-th variable of the coefficient ring $\mathrm{MvPowerSeries}\,(\mathrm{Fin}\,n)\,R$. Only the existence of such an $e$ is claimed, not a particular choice of isomorphism.
--
--   This is the elementary identification of a power series ring in $n+1$ variables with a one-variable power series ring over the power series ring in the remaining $n$ variables, in the form needed for inductive arguments. It serves as the induction step for transferring one-variable facts about formal power series to $\mathcal{O}[[X_1,\dots,X_n]]$, and is used in the treatment of Cohen-style power series presentations of complete local rings arising in deformation theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PowerSeries.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem MvPowerSeries.exists_algEquiv_powerSeries_fin_succ (R : Type u) [CommSemiring R] (n : ℕ) : ∃ e : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R), e (MvPowerSeries.X 0) = PowerSeries.X ∧ ∀ i : Fin n, e (MvPowerSeries.X i.succ) = PowerSeries.C (MvPowerSeries.X i) := by sorry
