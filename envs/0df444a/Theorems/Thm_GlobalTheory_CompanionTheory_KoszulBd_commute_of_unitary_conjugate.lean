-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_commute_of_unitary_conjugate
-- name    : GlobalTheory.CompanionTheory.KoszulBd.commute_of_unitary_conjugate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:13.383228+00:00
-- url     : https://prove2.me/theorems/d61be382-340d-4286-8f1b-7e9472030dd4
-- title:
--   Koszul Bd: commute of unitary conjugate
-- statement:
--   The Koszul Bd construction uses the commute of unitary conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L68-L84

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
omit [DecidableEq ι] [Algebra ℂ R]

theorem GlobalTheory.CompanionTheory.KoszulBd.commute_of_unitary_conjugate (T G : R) (L A : ι → R) (hTA : ∀ k, Commute T (A k)) (hGL : ∀ k, Commute G (L k))
    (h : ∑ k, (T * L k - L k * T) * A k + ∑ k, L k * (G * A k - A k * G) = 0) :
    Commute (T + G) (∑ k, L k * A k) := by sorry
