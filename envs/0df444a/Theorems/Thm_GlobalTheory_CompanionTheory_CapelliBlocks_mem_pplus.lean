-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_mem_pplus
-- name    : GlobalTheory.CompanionTheory.CapelliBlocks.mem_pplus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:05.83581+00:00
-- url     : https://prove2.me/theorems/f01db634-c09e-405c-9b2c-01bae7735c1e
-- title:
--   Capelli Blocks: mem pplus
-- statement:
--   The Capelli Blocks construction uses the mem pplus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L63-L71

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CapelliBlocks.mem_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (v : V) : E a b v ∈ pplus ε E := by sorry
