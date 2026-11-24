-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSSmLin_inG_add
-- name    : GlobalTheory.CompanionTheory.DSSmLin.inG_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:30.354966+00:00
-- url     : https://prove2.me/theorems/2ba43e69-3698-4369-964c-2747d70befca
-- title:
--   DSSm Lin: in G add
-- statement:
--   The DSSm Lin construction uses the in G add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MulMemUJset.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MulMemUJset.lean#L22-L25

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSSmLin
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.DSSmLin.inG_add {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by sorry
