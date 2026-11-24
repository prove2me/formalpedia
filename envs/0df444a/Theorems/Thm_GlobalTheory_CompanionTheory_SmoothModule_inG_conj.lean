-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_inG_conj
-- name    : GlobalTheory.CompanionTheory.SmoothModule.inG_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:47.589785+00:00
-- url     : https://prove2.me/theorems/dacee004-5836-4821-a6e4-08ee54f91c95
-- title:
--   Smooth Module: in G conj
-- statement:
--   The Smooth Module construction uses the in G conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L146-L152

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.SmoothModule.inG_conj {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    inG ε (g * X * g⁻¹) := by sorry
