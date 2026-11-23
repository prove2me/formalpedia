-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_homotopy_ring
-- name    : GlobalTheory.CompanionTheory.DSICKoszul.homotopy_ring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:08.50782+00:00
-- url     : https://prove2.me/theorems/9f1afd11-e4e7-418b-8056-6a293292a097
-- title:
--   DSICKoszul: homotopy ring
-- statement:
--   The DSICKoszul construction uses the homotopy ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean#L17-L41

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

theorem GlobalTheory.CompanionTheory.DSICKoszul.homotopy_ring (A D an cr : ι → R)
    (h1 : ∀ i j, Commute (an i) (D j)) (h2 : ∀ i j, Commute (cr i) (A j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0)
    (h4 : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, A i * an i) * (∑ j, D j * cr j) + (∑ j, D j * cr j) * (∑ i, A i * an i) =
      ∑ i, A i * D i + ∑ i, cr i * an i := by sorry
