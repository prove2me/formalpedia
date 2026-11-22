-- Prove2me | Theorems.Thm_MasulloRH_negative_lag_radial_measurement_rigidity
-- name    : MasulloRH.negative_lag_radial_measurement_rigidity
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T23:58:51.471378+00:00
-- url     : https://prove2.me/theorems/073b9a0c-65d6-497c-94b8-fc236c77f8d6
-- title:
--   A vanishing folded negative-lag measurement forces the complex radial mask to vanish
-- statement:
--   Let $\alpha,L>0$ and $U:(0,L)\to\mathbb C$ be Lebesgue integrable. Write $q=e^{-2\alpha L}$, and consider the folded negative-lag profile at the complementary endpoint $u=L-d$,
--   $$W(u)=\int_0^u e^{2\alpha a}U(a)\,da+q\int_u^L e^{2\alpha a}U(a)\,da.$$
--   If $W(u)=0$ for Lebesgue-almost every $u\in(0,L)$, then $U=0$ almost everywhere on that cell and $\int_0^L U(a)\,da=0$. This is the rigidity step for a radial output mask in the first principal Euler-cell model: cancellation of the diffuse folded pole on the entire open negative-lag gap excludes a mask with nonzero cell mean.
-- source:
--   New supporting theorem for the Masullo mission. The principal train and rank-one pole profile are described in mission comments 2f2f1d62-3a43-44d0-a05b-3ddd9702b1d0 and a30cf392-64c3-4fb0-96f3-7ff493aa7e40. Folding the pole autocorrelation on the first negative-lag interval yields the two weighted integrals, up to a nonzero scalar factor. The formal statement starts from those integrals and establishes their injectivity.

import Mathlib

open Filter MeasureTheory Set
open scoped Topology

theorem MasulloRH.negative_lag_radial_measurement_rigidity (α L : ℝ) (hα : 0 < α) (hL : 0 < L) (U : ℝ → ℂ)
    (hU : IntervalIntegrable U volume 0 L)
    (hW : ∀ᵐ u ∂volume.restrict (Ioo 0 L),
      (∫ a in (0 : ℝ)..u, (Real.exp (2 * α * a) : ℂ) * U a) +
        (Real.exp (-(2 * α * L)) : ℂ) *
          (∫ a in u..L, (Real.exp (2 * α * a) : ℂ) * U a) = 0) :
    (∀ᵐ a ∂volume.restrict (Ioo 0 L), U a = 0) ∧ (∫ a in (0 : ℝ)..L, U a) = 0 := by sorry
