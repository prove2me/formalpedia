-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_flat_symm_apply
-- name    : GlobalTheory.WeilM.flat_symm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:38.030799+00:00
-- url     : https://prove2.me/theorems/68e25e7e-cd22-4583-b6ec-569941a948c3
-- title:
--   Weil M: flat symm apply
-- statement:
--   The Weil M construction uses the flat symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L87-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L87-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}

theorem GlobalTheory.WeilM.flat_symm_apply (σ : κ ≃ α × β) (u : κ → R) (i : α) (j : β) : (flat σ).symm u i j = u (σ.symm (i, j)) := by sorry
