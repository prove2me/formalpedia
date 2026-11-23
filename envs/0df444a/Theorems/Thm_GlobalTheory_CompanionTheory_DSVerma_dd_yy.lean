-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_dd_yy
-- name    : GlobalTheory.CompanionTheory.DSVerma.dd_yy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:20.734806+00:00
-- url     : https://prove2.me/theorems/c327628e-c124-4664-9f9d-2f2057cf42f3
-- title:
--   DSVerma: dd yy
-- statement:
--   The DSVerma construction uses the dd yy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L136-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L136-L151

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

theorem GlobalTheory.CompanionTheory.DSVerma.dd_yy (a c : Fin n) (j : NC ε) :
    dd ε a c * yy j - yy j * dd ε a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0 := by sorry
