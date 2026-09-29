-- Prove2me | Theorems.Thm_MvPowerSeries_maximalIdeal_eq_comap_constantCoeff
-- name    : MvPowerSeries.maximalIdeal_eq_comap_constantCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/63cfd843-2eef-5c8c-89c0-61cadc978aaa
-- title:
--   Maximal ideal of a multivariate power series ring
-- statement:
--   Let $\sigma$ be any index type and let $R$ be a commutative ring which is local (in the sense of Mathlib's `IsLocalRing`, i.e. its non-units form an ideal). Then the power series ring $\mathrm{MvPowerSeries}\ \sigma\ R = R[[X_i : i \in \sigma]]$, which is again local, has maximal ideal equal to the preimage (`Ideal.comap`) of the maximal ideal of $R$ along the constant-coefficient ring homomorphism $\mathrm{constantCoeff} : R[[X_i]] \to R$. Explicitly, a multivariate formal power series $\varphi$ is a non-unit of $R[[X_i : i \in \sigma]]$ if and only if its constant term $\mathrm{constantCoeff}\ \varphi$ is a non-unit of $R$, so that the maximal ideal consists of those $\varphi$ whose constant term lies in the maximal ideal of $R$. No finiteness or cardinality hypothesis is imposed on the index type $\sigma$, and $R$ is not assumed Noetherian or complete.
--
--   This is the standard description of the maximal ideal of a formal power series ring over a local ring, used throughout when one works in local rings of the shape $\mathcal{O}[[X_1,\dots,X_n]]$, as in presentations of deformation rings and of local Hecke algebras. Within the development it supports [`MvPowerSeries.exists_coords_of_quotient_span_finite_free`](thm.html#MvPowerSeries.exists_coords_of_quotient_span_finite_free).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_maximalIdeal_eq_comap_constantCoeff.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem MvPowerSeries.maximalIdeal_eq_comap_constantCoeff {σ : Type u} {R : Type v} [CommRing R] [IsLocalRing R] : IsLocalRing.maximalIdeal (MvPowerSeries σ R) = (IsLocalRing.maximalIdeal R).comap (MvPowerSeries.constantCoeff (σ := σ) (R := R)) := by sorry
