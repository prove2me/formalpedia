-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_inner_sD
-- name    : GlobalTheory.CompanionTheory.DSUniq.inner_sD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:06.56693+00:00
-- url     : https://prove2.me/theorems/9d19c5c7-a37f-4772-be33-015e3eb6b69d
-- title:
--   DSUniq: inner s D
-- statement:
--   The DSUniq construction uses the inner s D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L246-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L246-L246

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset WithLp
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSUniq
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight Cas)
open PI.UpqRep (lowK IsURepOn IsIrredOn UJset IsDS)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (Cyc LocFin IsMin IsKMod MultAlg KModExists OrthCyc mem_cyc cyc_stab ev)
open ReciprocityTheory.ChartRestriction.DS (genSub IsDerivedOn)
open ReciprocityTheory.ChartRestriction.DS.USum (sD sE sσ ofP toP lift)
variable {n : ℕ}
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {D : Submodule ℂ H} {D' : Submodule ℂ H'} {E : Fin n → Fin n → Module.End ℂ D}
  {E' : Fin n → Fin n → Module.End ℂ D'} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.DSUniq.inner_sD (x y : sD D D') : ⟪x, y⟫_ℂ = ⟪(toP x).1, (toP y).1⟫_ℂ + ⟪(toP x).2, (toP y).2⟫_ℂ := by sorry
