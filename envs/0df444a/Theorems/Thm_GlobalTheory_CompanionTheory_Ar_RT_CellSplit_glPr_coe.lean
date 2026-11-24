-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_glPr_coe
-- name    : GlobalTheory.CompanionTheory.Ar.RT.CellSplit.glPr_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:53.273279+00:00
-- url     : https://prove2.me/theorems/f801eb0c-5146-4de3-b6da-093ef531c673
-- title:
--   Cell Split: gl Pr coe
-- statement:
--   The Cell Split construction uses the gl Pr coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L69-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L69-L69

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
variable {S E₁ E₂ : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂)
variable {n : Type} [DecidableEq n]
variable [Fintype n]

theorem GlobalTheory.CompanionTheory.Ar.RT.CellSplit.glPr_coe (x : GL n S) : ((glPr s x : GL n E₁) : Matrix n n E₁) = (x : Matrix n n S).map (pr₁ s) := by sorry
