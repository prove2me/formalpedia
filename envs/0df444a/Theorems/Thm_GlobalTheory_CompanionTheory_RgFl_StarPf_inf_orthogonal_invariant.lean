-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_StarPf_inf_orthogonal_invariant
-- name    : GlobalTheory.CompanionTheory.RgFl.StarPf.inf_orthogonal_invariant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:51.612938+00:00
-- url     : https://prove2.me/theorems/f74aac74-b9fc-492e-a714-7b9c62140692
-- title:
--   Star Pf: inf orthogonal invariant
-- statement:
--   The Star Pf construction uses the inf orthogonal invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean#L30-L41

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

theorem GlobalTheory.CompanionTheory.RgFl.StarPf.inf_orthogonal_invariant [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hs : StarClosed ρ) {U W : Submodule ℂ V}
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) :
    ∀ h, ∀ x ∈ Uᗮ ⊓ W, ρ h x ∈ Uᗮ ⊓ W := by sorry
