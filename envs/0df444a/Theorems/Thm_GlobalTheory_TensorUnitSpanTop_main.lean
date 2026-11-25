-- Prove2me | Theorems.Thm_GlobalTheory_TensorUnitSpanTop_main
-- name    : GlobalTheory.TensorUnitSpanTop.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:45.14683+00:00
-- url     : https://prove2.me/theorems/681baf5d-de31-5626-8766-eb33c5ef9d57
-- title:
--   Tensor Unit Span Top: main
-- statement:
--   The Tensor Unit Span Top construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanOneTmulEqTop.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanOneTmulEqTop.lean#L33-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanOneTmulEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorUnitSpanTop
open TensorProduct

theorem GlobalTheory.TensorUnitSpanTop.main : ∀ {R M : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : AddCommGroup M] [inst_3 : Module R M] {ι : Type} (f : ι → M), Submodule.span R (Set.range f) = ⊤ → Submodule.span (IsLocalRing.ResidueField R) (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by sorry
