-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_qdet
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.bd_qdet
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:13.960919+00:00
-- url     : https://prove2.me/theorems/daa36595-8107-46e6-8b81-b9b4e45753fe
-- title:
--   Casselman Osborne: bd qdet
-- statement:
--   The Casselman Osborne construction uses the bd qdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L180-L182

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.bd_qdet (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (u : ℂ) (x : Ch ε V) :
    bd ε E (lift ε (qdet E u) x) = lift ε (qdet E u) (bd ε E x) := by sorry
