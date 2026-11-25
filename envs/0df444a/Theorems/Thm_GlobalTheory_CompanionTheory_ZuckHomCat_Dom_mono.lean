-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckHomCat_Dom_mono
-- name    : GlobalTheory.CompanionTheory.ZuckHomCat.Dom.mono
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:45.256344+00:00
-- url     : https://prove2.me/theorems/1645a1f1-160e-5480-a75e-b45d6a061ee6
-- title:
--   Dom: mono
-- statement:
--   The Dom construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L47-L49

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckHomCat.Dom.mono {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X ψ) (hle : ∀ x, φ x ≤ ψ x) : Dom X φ := by sorry
