-- Prove2me | Theorems.Thm_GlobalTheory_RankFibre_indScal_lift_apply
-- name    : GlobalTheory.RankFibre.indScal_lift_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:16.240181+00:00
-- url     : https://prove2.me/theorems/b18e2b96-4a75-4285-b6ee-6d88e7497df3
-- title:
--   Rank Fibre: ind Scal lift apply
-- statement:
--   The Rank Fibre construction uses the ind Scal lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InducedScalarIrreducible.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InducedScalarIrreducible.lean#L39-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InducedScalarIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RankFibre.indScal_lift_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b)
    (x : GL (Fin (a + b)) k) : TensorProduct.lid ℂ ℂ ((indScalLift ν β a b hf).1.1 x) = f x := by sorry
