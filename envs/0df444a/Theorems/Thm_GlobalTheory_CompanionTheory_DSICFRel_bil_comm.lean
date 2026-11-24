-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_bil_comm
-- name    : GlobalTheory.CompanionTheory.DSICFRel.bil_comm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:27.396972+00:00
-- url     : https://prove2.me/theorems/aba84595-7c1b-4e94-b01e-211f19d1d7f4
-- title:
--   DSICFRel: bil comm
-- statement:
--   The DSICFRel construction uses the bil comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L32-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L32-L83

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel

theorem GlobalTheory.CompanionTheory.DSICFRel.bil_comm {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (m m' : ι → ι → ℂ) :
    bil c a m * bil c a m' - bil c a m' * bil c a m =
      bil c a (fun i l => ∑ k, m i k * m' k l - ∑ k, m' i k * m k l) := by sorry
