-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_comm_cre
-- name    : GlobalTheory.CompanionTheory.KoszulBd.comm_cre
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:33.329898+00:00
-- url     : https://prove2.me/theorems/817db10d-3cc8-4167-8ecc-a3103140e216
-- title:
--   Koszul Bd: comm cre
-- statement:
--   The Koszul Bd construction uses the comm cre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L112-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L112-L130

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

theorem GlobalTheory.CompanionTheory.KoszulBd.comm_cre (A C : ι → R) (q : ι → ι → ℂ) (hCC : ∀ i j, C i * C j + C j * C i = 0)
    (hAC : ∀ i j, A i * C j + C j * A i = if i = j then 1 else 0) (k : ι) :
    (∑ i, ∑ j, q i j • (C i * A j)) * C k - C k * (∑ i, ∑ j, q i j • (C i * A j)) = ∑ i, q i k • C i := by sorry
