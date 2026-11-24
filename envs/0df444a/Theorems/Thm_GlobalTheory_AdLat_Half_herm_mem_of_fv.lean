-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Half_herm_mem_of_fv
-- name    : GlobalTheory.AdLat.Half.herm_mem_of_fv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:58:35.318476+00:00
-- url     : https://prove2.me/theorems/88c3f55b-1887-48da-b7f3-0d7202c6ef67
-- title:
--   Half: herm mem of fv
-- statement:
--   The Half construction uses the herm mem of fv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L79-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L79-L112

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

theorem GlobalTheory.AdLat.Half.herm_mem_of_fv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : Set E) (L : Set (Fin n → E)) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ y ∈ L, _root_.GlobalTheory.AdLat.hermA c G z (_root_.GlobalTheory.AdLat.fv F y) ∈
      _root_.GlobalTheory.AdLat.hat1 F J)
    (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F J := by sorry
