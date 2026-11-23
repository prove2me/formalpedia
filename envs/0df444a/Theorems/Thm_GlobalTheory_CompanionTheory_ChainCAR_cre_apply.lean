-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_cre_apply
-- name    : GlobalTheory.CompanionTheory.ChainCAR.cre_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:59.362426+00:00
-- url     : https://prove2.me/theorems/5202e301-71c6-4aba-a3f8-9eb128132f7a
-- title:
--   Chain CAR: cre apply
-- statement:
--   The Chain CAR construction uses the cre apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L63-L64

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ChainCAR.cre_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := by sorry
