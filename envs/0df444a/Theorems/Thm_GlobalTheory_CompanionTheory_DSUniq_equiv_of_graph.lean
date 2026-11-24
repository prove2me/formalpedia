-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_equiv_of_graph
-- name    : GlobalTheory.CompanionTheory.DSUniq.equiv_of_graph
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:35:54.61794+00:00
-- url     : https://prove2.me/theorems/caad7c94-cab5-48f8-bd44-eb6a869a2afc
-- title:
--   DSUniq: equiv of graph
-- statement:
--   The DSUniq construction uses the equiv of graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L22-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L22-L80

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

theorem GlobalTheory.CompanionTheory.DSUniq.equiv_of_graph {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {G : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hI : IsIrredOn G σ) (hI' : IsIrredOn G σ')
    (Y : Submodule ℂ (WithLp 2 (H × H'))) (hc : IsClosed (Y : Set (WithLp 2 (H × H'))))
    (hst : ∀ g ∈ G, ∀ y ∈ Y, sσ σ σ' g y ∈ Y) (hn : ∀ y ∈ Y, ‖(ofLp y).1‖ = ‖(ofLp y).2‖)
    {y₀ : WithLp 2 (H × H')} (hy₀ : y₀ ∈ Y) (h0 : y₀ ≠ 0) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ G, ∀ x, U (σ g x) = σ' g (U x) := by sorry
