-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_dd_comm
-- name    : GlobalTheory.CompanionTheory.DSVerma.dd_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:13.487625+00:00
-- url     : https://prove2.me/theorems/1076f840-0c6b-44e7-8a4e-32a72d206ecb
-- title:
--   DSVerma: dd comm
-- statement:
--   The DSVerma construction uses the dd comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L129-L134

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
open MvPolynomial

theorem GlobalTheory.CompanionTheory.DSVerma.dd_comm (a b c d : Fin n) : Commute (dd ε a b) (dd ε c d) := by sorry
