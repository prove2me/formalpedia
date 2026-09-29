-- Prove2me | Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
-- name    : MvPowerSeries.isAdicComplete_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/d82e55d2-acdc-5885-8a08-b125e8a7b2f5
-- title:
--   Adic completeness of multivariate power series over a complete local ring
-- statement:
--   Let $\sigma$ be a finite index type and let $R$ be a commutative ring which is local, with maximal ideal $\mathfrak m_R =$ `IsLocalRing.maximalIdeal R`, and which is adically complete for $\mathfrak m_R$, i.e. $R$ is both $\mathfrak m_R$-adically Hausdorff (every element lying in $\bigcap_n \mathfrak m_R^n$ is zero) and $\mathfrak m_R$-adically precomplete (every sequence $(a_n)$ with $a_{n+1} \equiv a_n \bmod \mathfrak m_R^{n}$ has a limit, i.e. some $a$ with $a \equiv a_n \bmod \mathfrak m_R^{n}$ for all $n$). The conclusion is that the ring $R[[X_i : i \in \sigma]]$ of formal power series in the variables indexed by $\sigma$, which is again a local ring, is adically complete for its own maximal ideal `IsLocalRing.maximalIdeal (MvPowerSeries σ R)`, namely the ideal of power series whose constant term lies in $\mathfrak m_R$. No Noetherian hypothesis on $R$ is imposed, and $\sigma$ is only required to be finite, with no further structure.
--
--   This is the standard fact that a formal power series ring in finitely many variables over a complete local ring is again complete for its maximal ideal; the typical instance in the present development is $\mathcal O[[X_1,\dots,X_n]]$ for $\mathcal O$ the ring of integers of a $p$-adic field. It supplies the completeness hypotheses used in the deformation-theoretic and patching parts of the argument, for instance in the construction of adic completions of tensor products and in the verification of patching data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_isAdicComplete_maximalIdeal.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem MvPowerSeries.isAdicComplete_maximalIdeal {σ : Type u} {R : Type v} [Finite σ] [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by sorry
