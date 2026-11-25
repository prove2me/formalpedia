-- Prove2me | Theorems.Thm_GlobalTheory_CayleyUnitary_cayley_mem_UJ
-- name    : GlobalTheory.CayleyUnitary.cayley_mem_UJ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:02:40.651402+00:00
-- url     : https://prove2.me/theorems/34486e64-3003-4967-bb67-11aed6146ed0
-- title:
--   Cayley Unitary: cayley mem UJ
-- statement:
--   The Cayley Unitary construction uses the cayley mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CayleyTransformSkewMemUnitaryGroup.lean#L19-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CayleyTransformSkewMemUnitaryGroup.lean#L19-L51

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CayleyUnitary
open Formalism.UG

theorem GlobalTheory.CayleyUnitary.cayley_mem_UJ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E) :
    J.det ≠ 0 → cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by sorry
