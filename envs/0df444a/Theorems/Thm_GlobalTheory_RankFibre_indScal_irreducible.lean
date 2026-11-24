-- Prove2me | Theorems.Thm_GlobalTheory_RankFibre_indScal_irreducible
-- name    : GlobalTheory.RankFibre.indScal_irreducible
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:37.317828+00:00
-- url     : https://prove2.me/theorems/940ee2ce-5ccc-4c90-8815-63fdcffc615a
-- title:
--   Rank Fibre: ind Scal irreducible
-- statement:
--   The Rank Fibre construction uses the ind Scal irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InducedScalarIrreducible.lean#L63-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InducedScalarIrreducible.lean#L63-L86

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

theorem GlobalTheory.RankFibre.indScal_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by sorry
