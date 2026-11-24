-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_sq_ring
-- name    : GlobalTheory.CompanionTheory.DSICKoszul.sq_ring
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:50.116752+00:00
-- url     : https://prove2.me/theorems/b1342a1a-1571-4c20-a349-6249253d0594
-- title:
--   DSICKoszul: sq ring
-- statement:
--   The DSICKoszul construction uses the sq ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L45-L60

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.DSICKoszul.sq_ring (A an : ι → R)
    (h1 : ∀ i j, Commute (an i) (A j)) (h2 : ∀ i j, Commute (A i) (A j))
    (h4 : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, A i * an i) * (∑ j, A j * an j) + (∑ j, A j * an j) * (∑ i, A i * an i) = 0 := by sorry
