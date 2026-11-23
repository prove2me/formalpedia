-- Prove2me | Theorems.Thm_NoHair_Weyl_vacuum_rod_profile_iff_regular_boundary_data
-- name    : NoHair.Weyl.vacuum_rod_profile_iff_regular_boundary_data
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:33:26.860748+00:00
-- url     : https://prove2.me/theorems/f4aa2230-2c71-4464-b41b-cfd9aacb93fd
-- title:
--   For vacuum Ernst solutions the Kerr rod estimates are equivalent to regular weighted boundary data
-- statement:
--   For a vacuum Ernst solution and fixed vacuum Kerr parameters, the normalized one-interval boundary estimates are equivalent to the existence of weighted angular data on the closed prolate rectangle. The forward direction uses Ernst boundary uniqueness and the explicit Kerr data. The reverse direction follows directly from regularity of the weighted data and the signs of the inward norm derivatives.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), §§6.2–6.7, https://arxiv.org/abs/0806.0016. The compactified variables and angular derivative criterion here are an explicit sufficient condition for the platform’s normalized rod estimates.

import Definitions.Def_NoHair_regularRodBoundaryData

open NoHair NoHair.Weyl Set
open scoped ContDiff Manifold

theorem NoHair.Weyl.vacuum_rod_profile_iff_regular_boundary_data (u : ErnstPotentials) (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (hu : u.IsSolution) :
    let ℓ := Real.sqrt (m^2-a^2)
    let J := m*a
    HasProfileEstimates u (rodBoundaryProfile m ℓ J) ↔ Nonempty (RegularRodBoundaryData u m ℓ J) := by
  sorry
