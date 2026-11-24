-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_length_subquot
-- name    : GlobalTheory.CoeffExt.length_subquot
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:15:04.053285+00:00
-- url     : https://prove2.me/theorems/88cee14f-8e22-4aa7-bb1e-f8c360458f6b
-- title:
--   Coeff Ext: length subquot
-- statement:
--   The Coeff Ext construction uses the length subquot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L32-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L32-L67

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W W' : Type} [AddCommGroup W]
  [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W'] [IsScalarTower O O' W'] {ι : Type}
  [Fintype ι]

theorem GlobalTheory.CoeffExt.length_subquot (E : W' ≃ₗ[O] (ι → W)) (S' N' : Submodule O' W') (S N : Submodule O W)
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) (hN : ∀ x, x ∈ N' ↔ ∀ i, E x i ∈ N) :
    Module.length O (↥S' ⧸ N'.comap S'.subtype) =
      Fintype.card ι * Module.length O (↥S ⧸ N.comap S.subtype) := by sorry
