-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_comm_ann
-- name    : GlobalTheory.CompanionTheory.KoszulBd.comm_ann
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:14.924718+00:00
-- url     : https://prove2.me/theorems/cb489627-83eb-4f88-b747-73c3d5343c5f
-- title:
--   Koszul Bd: comm ann
-- statement:
--   The Koszul Bd construction uses the comm ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L86-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L86-L110

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]

theorem GlobalTheory.CompanionTheory.KoszulBd.comm_ann (A C : ι → R) (q : ι → ι → ℂ) (hAA : ∀ i j, A i * A j + A j * A i = 0)
    (hAC : ∀ i j, A i * C j + C j * A i = if i = j then 1 else 0) (k : ι) :
    (∑ i, ∑ j, q i j • (C i * A j)) * A k - A k * (∑ i, ∑ j, q i j • (C i * A j)) = -∑ j, q k j • A j := by sorry
