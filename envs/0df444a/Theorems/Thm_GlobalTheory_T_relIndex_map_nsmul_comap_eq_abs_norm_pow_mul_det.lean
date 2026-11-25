-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det
-- name    : GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:42.934901+00:00
-- url     : https://prove2.me/theorems/f75fae0d-3432-4d59-b3fd-3dc42513b39e
-- title:
--   T: rel Index map nsmul comap eq abs norm pow mul det
-- statement:
--   The T construction uses the rel Index map nsmul comap eq abs norm pow mul det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexMapNsmulComapEqAbsNormDetStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexMapNsmulComapEqAbsNormDetStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexMapNsmulComapEqAbsNormDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexMapNsmulComapEqAbsNormDetStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det : ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by sorry
