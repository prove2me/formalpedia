-- Prove2me | Theorems.Thm_GlobalTheory_SBProd_isLocallyConstant_filter
-- name    : GlobalTheory.SBProd.isLocallyConstant_filter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:31:36.718016+00:00
-- url     : https://prove2.me/theorems/63f64146-fc55-45b7-b9b0-06fbc4314f1f
-- title:
--   SBProd: is Locally Constant filter
-- statement:
--   The SBProd construction uses the is Locally Constant filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecomposition.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecomposition.lean#L20-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.SBProd

theorem GlobalTheory.SBProd.isLocallyConstant_filter {H ι : Type} [TopologicalSpace H] (F : Finset ι) (U : ι → Set H)
    (hU : ∀ i, IsClopen (U i)) : IsLocallyConstant fun a => F.filter (fun i => a ∈ U i) := by sorry
