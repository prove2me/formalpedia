-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_StarPf_restrictAlg_coe
-- name    : GlobalTheory.CompanionTheory.RgFl.StarPf.restrictAlg_coe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:44.123525+00:00
-- url     : https://prove2.me/theorems/73d77747-a30d-4d3b-8cb7-169de7839629
-- title:
--   Star Pf: restrict Alg coe
-- statement:
--   The Star Pf construction uses the restrict Alg coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean#L27-L28

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.StarPf
variable {A V : Type} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.RgFl.StarPf.restrictAlg_coe [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (h : A) (x : W) : ((restrictAlg ρ W hW h x : W) : V) = ρ h x := by sorry
