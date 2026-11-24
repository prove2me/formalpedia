-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainHighest_kRel_map
-- name    : GlobalTheory.CompanionTheory.ChainHighest.kRel_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:32.397372+00:00
-- url     : https://prove2.me/theorems/85502da1-a1db-44af-a11e-9de22b5ffe4a
-- title:
--   Chain Highest: k Rel map
-- statement:
--   The Chain Highest construction uses the k Rel map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsCocycleOfMapToDegreeOneTerm.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsCocycleOfMapToDegreeOneTerm.lean#L16-L22

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsCocycleOfMapToDegreeOneTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainHighest
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)

theorem GlobalTheory.CompanionTheory.ChainHighest.kRel_map {n : ℕ} {A B : Type} [Ring A] [Ring B] (ε : Fin n → Bool) (f : A →+* B)
    (F : Fin n → Fin n → A) (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by sorry
