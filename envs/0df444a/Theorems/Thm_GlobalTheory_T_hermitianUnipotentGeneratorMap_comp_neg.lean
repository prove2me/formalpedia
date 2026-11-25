-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianUnipotentGeneratorMap_comp_neg
-- name    : GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:19.123502+00:00
-- url     : https://prove2.me/theorems/0c25362b-9f2b-4871-96a0-f2cab8842c5a
-- title:
--   T: hermitian Unipotent Generator Map comp neg
-- statement:
--   The T construction uses the hermitian Unipotent Generator Map comp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianUnipotentGeneratorMapCompNegStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianUnipotentGeneratorMapCompNegStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapCompNeg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapCompNegStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) → ∀ v : V, GlobalTheory.RowStab.gen H J e ρ c (GlobalTheory.RowStab.gen H J e (-ρ) c' v) = v := by sorry
