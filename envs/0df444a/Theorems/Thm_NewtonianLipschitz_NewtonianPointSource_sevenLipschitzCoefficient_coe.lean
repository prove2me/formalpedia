-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_sevenLipschitzCoefficient_coe
-- name    : NewtonianLipschitz.NewtonianPointSource.sevenLipschitzCoefficient_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:28.614775+00:00
-- url     : https://prove2.me/theorems/a6a8279c-4054-4750-aaaa-5e3a0995e994
-- title:
--   Newtonian Point Source: seven Lipschitz Coefficient coe
-- statement:
--   The Newtonian Point Source construction uses the seven Lipschitz Coefficient coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean#L25-L33
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean#L25-L33

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexImproved
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.sevenLipschitzCoefficient_coe
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d) :
    ((NewtonianPointSource.sevenLipschitzCoefficient d M hd : ℝ≥0) : ℝ) =
      7 * (M : ℝ) / d ^ 3 := by sorry
