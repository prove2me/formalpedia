-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_sum_pick
-- name    : GlobalTheory.CompanionTheory.KoszulBd.sum_pick
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:52:29.2238+00:00
-- url     : https://prove2.me/theorems/d7b4fc6e-54de-4068-b4b9-ba51c2dff964
-- title:
--   Koszul Bd: sum pick
-- statement:
--   The Koszul Bd construction uses the sum pick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L16-L35

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

theorem GlobalTheory.CompanionTheory.KoszulBd.sum_pick {R : Type} [AddCommGroup R] [Module ℂ R] (f : Fin n → Fin n → R) (a b : Fin n) (P : Prop)
    [Decidable P] (hP : P → ε a = true ∧ ε b = false) (Q : NC ε → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q k ↔ P ∧ k.1.1 = a ∧ k.1.2 = b) :
    ∑ k : NC ε, (if Q k then (1 : ℂ) else 0) • f k.1.1 k.1.2 = if P then f a b else 0 := by sorry
