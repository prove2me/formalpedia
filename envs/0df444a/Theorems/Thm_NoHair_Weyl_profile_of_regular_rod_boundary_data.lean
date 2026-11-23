-- Prove2me | Theorems.Thm_NoHair_Weyl_profile_of_regular_rod_boundary_data
-- name    : NoHair.Weyl.profile_of_regular_rod_boundary_data
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:33:27.498266+00:00
-- url     : https://prove2.me/theorems/5de06575-a6ca-46bd-8b8d-eb9c5a63cd1e
-- title:
--   Angular boundary regularity gives uniform Weyl rod estimates, including at the corners
-- statement:
--   Write $q=1/(m+R)$ and $c=z/R$ in prolate coordinates. Suppose the rescaled axial norm and twist defect have continuous angular derivatives up to the closed $(q,c)$ rectangle, vanish on both axes, and have the flat limiting data at infinity. Strict inward norm slopes at the axes and positivity in the interior give a uniform positive lower norm ratio. Dividing by $1-c^2$ extends both ratios continuously to the corners, giving the global bounds and uniform asymptotic estimates in the Weyl comparison problem.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), §§6.2–6.7, https://arxiv.org/abs/0806.0016. The compactified variables and angular derivative criterion here are an explicit sufficient condition for the platform’s normalized rod estimates.

import Definitions.Def_NoHair_regularRodBoundaryData

open NoHair NoHair.Weyl Set
open scoped ContDiff Manifold

theorem NoHair.Weyl.profile_of_regular_rod_boundary_data (u : ErnstPotentials) (m ℓ J : ℝ) (hm : 0 < m) (hl : 0 ≤ ℓ)
    (h : RegularRodBoundaryData u m ℓ J) : HasProfileEstimates u (rodBoundaryProfile m ℓ J) := by
  sorry
