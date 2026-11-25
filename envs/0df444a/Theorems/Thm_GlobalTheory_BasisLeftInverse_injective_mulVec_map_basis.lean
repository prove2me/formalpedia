-- Prove2me | Theorems.Thm_GlobalTheory_BasisLeftInverse_injective_mulVec_map_basis
-- name    : GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:49.51969+00:00
-- url     : https://prove2.me/theorems/debaa564-b1f6-4242-9018-fcc6f92e129f
-- title:
--   Basis Left Inverse: injective mul Vec map basis
-- statement:
--   The Basis Left Inverse construction uses the injective mul Vec map basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InjectiveMulVecMapBasis.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InjectiveMulVecMapBasis.lean#L12-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InjectiveMulVecMapBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BasisLeftInverse

theorem GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis {E : Type} [Field E] {n : ℕ} (V : Submodule E (Fin n → E))
    (τ : E →+* ℂ) :
    Function.Injective (Matrix.mulVec (Matrix.of fun (k : Fin n) (i : Fin (Module.finrank E V)) =>
      τ (((Module.finBasis E V i : V) : Fin n → E) k))) := by sorry
