-- Prove2me | Theorems.Thm_GlobalTheory_QFam_IsFam_value_mul_denom
-- name    : GlobalTheory.QFam.IsFam.value_mul_denom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:55.984915+00:00
-- url     : https://prove2.me/theorems/22cfa597-0dee-4296-8b91-8b4835ccfc5e
-- title:
--   Is Fam: value mul denom
-- statement:
--   The Is Fam construction uses the value mul denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PermutedModularFamilySumEsymmSlashInvariant.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PermutedModularFamilySumEsymmSlashInvariant.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

theorem GlobalTheory.QFam.IsFam.value_mul_denom {ι : Type} {act : ι → SL(2, ℤ) → ι}
    {w : ℤ} {f : ι → ℍ → ℂ}
    (h : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w) = f (act i γ) τ := by sorry
