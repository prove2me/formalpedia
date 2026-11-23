-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_ReflLaws_hermE_eq_dot
-- name    : GlobalTheory.UnRep.ReflLaws.hermE_eq_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:34.443009+00:00
-- url     : https://prove2.me/theorems/8c85a05a-b5f8-453e-b335-ee7740a04fc8
-- title:
--   Refl Laws: herm E eq dot
-- statement:
--   The Refl Laws construction uses the herm E eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryQuasiReflectionLaws.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryQuasiReflectionLaws.lean#L16-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws
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
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflLaws
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.UnRep.ReflLaws.hermE_eq_dot (v x : Fin n → E) :
    _root_.GlobalTheory.UnRep.hermE c G v x = (G *ᵥ fun b => c (x b)) ⬝ᵥ v := by sorry
