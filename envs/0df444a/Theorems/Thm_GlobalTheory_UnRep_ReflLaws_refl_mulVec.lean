-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_ReflLaws_refl_mulVec
-- name    : GlobalTheory.UnRep.ReflLaws.refl_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:10.644382+00:00
-- url     : https://prove2.me/theorems/8b1593d4-4673-4054-a255-6a42c3b91a9e
-- title:
--   Refl Laws: refl mul Vec
-- statement:
--   The Refl Laws construction uses the refl mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryQuasiReflectionLaws.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryQuasiReflectionLaws.lean#L27-L38

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

theorem GlobalTheory.UnRep.ReflLaws.refl_mulVec (x : Fin n → E) (u : E) (v : Fin n → E) :
    _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x := by sorry
