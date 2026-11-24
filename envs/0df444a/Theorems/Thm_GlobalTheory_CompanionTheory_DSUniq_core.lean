-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_core
-- name    : GlobalTheory.CompanionTheory.DSUniq.core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:20.480614+00:00
-- url     : https://prove2.me/theorems/28ac5216-4f61-47b8-9e40-201c23854002
-- title:
--   DSUniq: core
-- statement:
--   The DSUniq construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L315-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L315-L342

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

theorem GlobalTheory.CompanionTheory.DSUniq.core (hM : MultAlg) (hO : OrthCyc) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) (hgl : GlRel E)
    (hun : IsUnitary ε E) (hF : LocFin ε E) (hm : IsMin ε E lam) {y : V} (hy0 : y ≠ 0)
    (hyK : KHighest ε E (lowK ε lam) y) (J : Module.End ℂ V) (hJ : ∀ a b x, J (E a b x) = E a b (J x))
    (hy : ⟪y, J y⟫_ℂ = 0) : (∃ c : ℂ, Cas E y = c • y) ∧ ∀ x ∈ Cyc E y, ⟪x, J x⟫_ℂ = 0 := by sorry
