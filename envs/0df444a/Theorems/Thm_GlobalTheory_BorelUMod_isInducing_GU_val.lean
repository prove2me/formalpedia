-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_isInducing_GU_val
-- name    : GlobalTheory.BorelUMod.isInducing_GU_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:07.513145+00:00
-- url     : https://prove2.me/theorems/490b0578-e9ca-58bc-8c76-dfdfa27648d9
-- title:
--   Borel UMod: is Inducing GU val
-- statement:
--   The Borel UMod construction uses the is Inducing GU val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnipLatIsOpenIsCompact.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnipLatIsOpenIsCompact.lean#L53-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.isInducing_GU_val {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Topology.IsInducing fun g : GU σ n => (g.1.val : Matrix (Fin n) (Fin n) L) := by sorry
