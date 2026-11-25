-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Half_herm_add_left
-- name    : GlobalTheory.AdLat.Half.herm_add_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:38.936662+00:00
-- url     : https://prove2.me/theorems/5c4223a5-7190-4557-ade2-a1ba5cfa6afe
-- title:
--   Half: herm add left
-- statement:
--   The Half construction uses the herm add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralTmulOneMulMemAdelicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Half
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.AdLat.Half.herm_add_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x + x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x' y := by sorry
