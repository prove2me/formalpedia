-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Half_herm_smul_left
-- name    : GlobalTheory.AdLat.Half.herm_smul_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:58:07.490283+00:00
-- url     : https://prove2.me/theorems/1f62bb2d-23e3-4e69-aa80-08638a7a0897
-- title:
--   Half: herm smul left
-- statement:
--   The Half construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L61-L64

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

theorem GlobalTheory.AdLat.Half.herm_smul_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (r • x) y = r * _root_.GlobalTheory.AdLat.hermA c G x y := by sorry
