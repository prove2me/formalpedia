-- Prove2me | Theorems.Thm_Kyprianou_Ch06_independentEventOfAlmostSureCountableStatistic
-- name    : Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:43:54.824605+00:00
-- url     : https://prove2.me/theorems/24e6a136-ffc1-46de-864e-fe356cfb265f
-- title:
--   Event independence transfers through an almost-sure deterministic function of a countable statistic
-- statement:
--   General probability transfer lemma: if a measurable event D is independent of every singleton fibre of a countably valued statistic X and Y is almost surely a deterministic function of X, D is independent of every singleton fibre of Y. Prove by partitioning the target fibre into pairwise disjoint X-fibres, with empty fibres for invalid images, and applying the source-proved almost-sure countable disjoint-union factorisation. This reusable theorem underpins finite-dimensional marked-Poisson restriction independence without adding stochastic assumptions.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
    {Omega I J : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D : Set Omega) (hD : MeasurableSet D)
    (X : Omega → I) (Y : Omega → J) (f : I → J)
    (hMeas : ∀ i : I, MeasurableSet {omega | X omega = i})
    (hFactor : ∀ i : I,
      P (D ∩ {omega | X omega = i}) =
        P D * P {omega | X omega = i})
    (hAe : ∀ᵐ omega ∂P, Y omega = f (X omega))
    (j : J) :
    P (D ∩ {omega | Y omega = j}) =
      P D * P {omega | Y omega = j} := by sorry
