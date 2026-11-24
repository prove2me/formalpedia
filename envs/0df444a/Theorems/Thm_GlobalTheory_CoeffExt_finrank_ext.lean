-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_finrank_ext
-- name    : GlobalTheory.CoeffExt.finrank_ext
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:15:31.360609+00:00
-- url     : https://prove2.me/theorems/27e761c3-9ae4-4eef-8698-885ba3d79d55
-- title:
--   Coeff Ext: finrank ext
-- statement:
--   The Coeff Ext construction uses the finrank ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L565-L581
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L565-L581

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

theorem GlobalTheory.CoeffExt.finrank_ext {O O' : Type} [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O']
    {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W']
    [IsScalarTower O O' W'] {ι : Type} [Fintype ι] (b : Basis ι O O') (E : W' ≃ₗ[O] (ι → W))
    (S' : Submodule O' W') (S : Submodule O W) [Module.Free O' ↥S'] [Module.Free O ↥S]
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : finrank O' ↥S' = finrank O ↥S := by sorry
