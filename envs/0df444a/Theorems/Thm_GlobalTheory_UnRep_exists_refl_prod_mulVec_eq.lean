-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_exists_refl_prod_mulVec_eq
-- name    : GlobalTheory.UnRep.exists_refl_prod_mulVec_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:09.319853+00:00
-- url     : https://prove2.me/theorems/0a8360ba-adc2-42c9-974f-52d84267d73c
-- title:
--   Un Rep: exists refl prod mul Vec eq
-- statement:
--   The Un Rep construction uses the exists refl prod mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean#L74-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean#L74-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory.UnRep.ReflStep

theorem GlobalTheory.UnRep.exists_refl_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by sorry
